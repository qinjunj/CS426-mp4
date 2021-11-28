//===----------------------------------------------------------------------===//
//
/// A register allocator simplified from RegAllocFast.cpp
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Statistic.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
#include "llvm/CodeGen/RegisterClassInfo.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"

#include <map>
#include <set>

using namespace llvm;

#define DEBUG_TYPE "regalloc"

STATISTIC(NumStores, "Number of stores added");
STATISTIC(NumLoads , "Number of loads added");

namespace {
  /// This is class where you will implement your register allocator in
  class RegAllocSimple : public MachineFunctionPass {
  public:
    static char ID;
    RegAllocSimple() : MachineFunctionPass(ID) {}

  private:
    /// Some information that might be useful for register allocation
    /// They are initialized in runOnMachineFunction
    MachineFrameInfo *MFI;
    MachineRegisterInfo *MRI;
    const TargetRegisterInfo *TRI;
    const TargetInstrInfo *TII;
    RegisterClassInfo RegClassInfo;
    
    MachineBasicBlock *MBB; 

    // maintain information about live registers

    // A live virtual register will be stored either in LiveVirtRegs or in SpillMap
    // record the mapping of virtual registers to stack slots
    std::map<Register, int> SpillMap;
    // record the mapping of virtual registers to physical registers
    std::map<Register, MCPhysReg> LiveVirtRegs; 
    // inverse mapping of physical registers to virtual registers
    std::map<MCPhysReg, Register> LivePhysRegs; 
    std::set<MCPhysReg> UsedInInstr; 
    std::set<MCPhysReg> UsedInBlk; 

  public:
    StringRef getPassName() const override { return "Simple Register Allocator"; }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesCFG();
      MachineFunctionPass::getAnalysisUsage(AU);
    }

    /// Ask the Machine IR verifier to check some simple properties
    /// Enabled with the -verify-machineinstrs flag in llc
    MachineFunctionProperties getRequiredProperties() const override {
      return MachineFunctionProperties().set(
          MachineFunctionProperties::Property::NoPHIs);
    }

    MachineFunctionProperties getSetProperties() const override {
      return MachineFunctionProperties().set(
          MachineFunctionProperties::Property::NoVRegs);
    }

    MachineFunctionProperties getClearedProperties() const override {
      return MachineFunctionProperties().set(
        MachineFunctionProperties::Property::IsSSA);
    }

  private:

    /*
      A few utility methods referenced from RegAllocFast.cpp.
    */
    bool isRegUsedInInstr(MCPhysReg PhysReg) {
      for (MCRegUnitIterator Units(PhysReg, TRI); Units.isValid(); ++Units) {
        if (UsedInInstr.count(*Units))
          return true;
      }
      return false;
    }

    bool isRegUsedInBlk(MCPhysReg PhysReg) {
      for (MCRegUnitIterator Units(PhysReg, TRI); Units.isValid(); ++Units) {
        if (UsedInBlk.count(*Units))
          return true;
      }
      return false;
    }

    void markRegUsedInInstr(MCPhysReg PhysReg) {
      for (MCRegUnitIterator Units(PhysReg, TRI); Units.isValid(); ++Units)
        UsedInInstr.insert(*Units);
    }

    void markRegUsedInBlk(MCPhysReg PhysReg) {
      for (MCRegUnitIterator Units(PhysReg, TRI); Units.isValid(); ++Units)
        UsedInBlk.insert(*Units);
    }

    int allocateStackSlot(Register VirtReg) {
      dbgs() << "before error\n";
      const TargetRegisterClass &RC = *MRI->getRegClass(VirtReg);
      dbgs() << "after error\n"; 
      unsigned Size = TRI->getSpillSize(RC);
      Align Alignment = TRI->getSpillAlign(RC);
      int FrameIndex = MFI->CreateSpillStackObject(Size, Alignment); 

      return FrameIndex; 
    }
    
    void spill(MachineBasicBlock::iterator Before, Register VirtReg, MCPhysReg PhysReg, bool kill, bool end) {
      int FrameIndex;
      if (SpillMap.count(VirtReg) > 0) { 
        FrameIndex = SpillMap[VirtReg];
      } else {
        FrameIndex = allocateStackSlot(VirtReg);
        SpillMap[VirtReg] = FrameIndex;
        if (!end) 
          LiveVirtRegs.erase(VirtReg); 
      }
      const TargetRegisterClass &RC = *MRI->getRegClass(VirtReg);
      TII->storeRegToStackSlot(*MBB, Before, PhysReg, kill, FrameIndex, &RC, TRI); 
      ++NumStores; 
    }

    void reload(MachineBasicBlock::iterator Before, Register VirtReg, MCPhysReg PhysReg) {
      int FrameIndex = SpillMap[VirtReg];
      const TargetRegisterClass &RC = *MRI->getRegClass(VirtReg);
      TII->loadRegFromStackSlot(*MBB, Before, PhysReg, FrameIndex, &RC, TRI);
      ++NumLoads;
    }

    // find available physical register or spilled physical register
    MCPhysReg findPhysReg(MachineInstr &MI, MachineOperand &MO, Register VirtReg) {
      MCPhysReg PhysReg = 0;
      const TargetRegisterClass &RC = *MRI->getRegClass(VirtReg);
      // Go through all available physical registers and find an unused physical register
      ArrayRef<MCPhysReg> AllocationOrder = RegClassInfo.getOrder(&RC);
      for (MCPhysReg Candidate : AllocationOrder) {
        if (isRegUsedInBlk(Candidate)) continue;
        PhysReg = Candidate; 
        break; 
      }
      // if not found
      if (!PhysReg) {
        // find a register curretly in use but not in UsedInInstr
        for (MCPhysReg SpillCandidate : UsedInBlk) {
          if (isRegUsedInInstr(SpillCandidate)) continue;
          PhysReg = SpillCandidate; 
          // Spill SpillCandidate
          Register SpillVirtReg = LivePhysRegs[PhysReg]; 
          if (LiveVirtRegs.count(SpillVirtReg) > 0) {
            MachineBasicBlock::iterator SpillBefore = (MachineBasicBlock::iterator)MI.getIterator(); // FIXME why next? 
            bool kill = MO.isKill(); 
            spill(SpillBefore, SpillVirtReg, SpillCandidate, kill, false); 
          }
          break; 
        }
      }
      return PhysReg; 
    }

    /// Allocate physical register for virtual register operand
    void allocateOperand(MachineInstr &MI, MachineOperand &MO, Register VirtReg, bool is_use) {
      // allocate physical register for a virtual register
      // VirtReg already has corresponding PhysReg (only possible for uses)
      if (LiveVirtRegs.count(VirtReg) > 0) {
        MCPhysReg PhysReg = LiveVirtRegs[VirtReg];
        MO.setReg(PhysReg);
        markRegUsedInInstr(PhysReg);
        markRegUsedInBlk(PhysReg);
        if (MO.isKill())  {
          LiveVirtRegs.erase(VirtReg); 
          if (SpillMap.count(VirtReg) > 0)
            SpillMap.erase(VirtReg);
        }
        return;
      }
      // VirtReg was spilled before 
      if (SpillMap.count(VirtReg) > 0) {
        MCPhysReg P = findPhysReg(MI, MO, VirtReg); 
        MachineBasicBlock::iterator LoadBefore = (MachineBasicBlock::iterator)MI.getIterator(); // FIXME where to insert?
        reload(LoadBefore, VirtReg, P);
        MO.setReg(P);
        markRegUsedInInstr(P);
        markRegUsedInBlk(P);
        if (!MO.isKill()) { LiveVirtRegs[VirtReg] = P; LivePhysRegs[P] = VirtReg; dbgs() << VirtReg << "live virt \n"; } 
        else SpillMap.erase(VirtReg); 
        return;
      }
      // VirtReg never met before
      MCPhysReg PhysReg = findPhysReg(MI, MO, VirtReg);
      MO.setReg(PhysReg); 
      markRegUsedInInstr(PhysReg);
      markRegUsedInBlk(PhysReg);
      LiveVirtRegs[VirtReg] = PhysReg;
      LivePhysRegs[PhysReg] = VirtReg; 
      dbgs() << VirtReg << "live virt \n";
    }

    void allocateInstruction(MachineInstr &MI) {
      dbgs() << "Instr: " << "\n"; 
      // find and allocate all virtual registers in MI
      UsedInInstr.clear(); 
      // Allocate uses first
      for (MachineOperand &MO : MI.operands()) {
        if (MO.isReg()) {
          Register Reg = MO.getReg();
          if (Reg.isVirtual() && MO.isUse()) {
            dbgs() << "Uses: \n"; 
            dbgs() << MO.getReg() << " " << MO.getSubReg() << "\n";
            MO.dump(); 
            allocateOperand(MI, MO, Reg, true); // FIXME getReg or getSubreg?  
          } else if (Reg.isPhysical()) {
            markRegUsedInInstr(Reg);
            markRegUsedInBlk(Reg); 
          }  
        }
      }
      // Allocate defs
      for (MachineOperand &MO : MI.operands()) { 
        if (MO.isReg()) {
          Register Reg = MO.getReg();
          if (Reg.isVirtual() && MO.isDef()) {
            dbgs() << "Defs: \n"; 
            dbgs() << MO.getReg() << " " << MO.getSubReg() << "\n";
            MO.dump(); 
            allocateOperand(MI, MO, Reg, false);  
          } else if (Reg.isPhysical()) {
            markRegUsedInInstr(Reg);
            markRegUsedInBlk(Reg); 
          }
        } 
      }
    }

    void allocateBasicBlock(MachineBasicBlock &MBB) {
      this->MBB = &MBB; 
      // allocate each instruction
      for (MachineInstr &MI : MBB) {
        // mark live-in registers as used
        for (MachineBasicBlock::RegisterMaskPair P : MBB.liveins()) {
          MCPhysReg Reg = P.PhysReg; 
          dbgs() << Reg << "\n";
          markRegUsedInBlk(Reg); 
        }
        allocateInstruction(MI);
      }
      // spill all live registers at the end
      dbgs() << LiveVirtRegs.size() << " map size\n"; 
      for (std::map<Register, MCPhysReg>::iterator it = LiveVirtRegs.begin(); it != LiveVirtRegs.end(); ++it) {
        MachineBasicBlock::iterator InsertBefore = (MachineBasicBlock::iterator)MBB.getFirstTerminator();
        dbgs() << it->first << "\n" << it->second << "\n";
        dbgs() << "after\n";
        if (it->first.isVirtual()) 
          spill(InsertBefore, it->first, it->second, false, true);
      }
    }

    bool runOnMachineFunction(MachineFunction &MF) override {
      dbgs() << "simple regalloc running on: " << MF.getName() << "\n";

      // outs() << "simple regalloc not implemented\n";
      // abort();

      // Get some useful information about the target
      MRI = &MF.getRegInfo();
      const TargetSubtargetInfo &STI = MF.getSubtarget();
      TRI = STI.getRegisterInfo();
      TII = STI.getInstrInfo();
      MFI = &MF.getFrameInfo();
      MRI->freezeReservedRegs(MF);
      RegClassInfo.runOnMachineFunction(MF);

      // Allocate each basic block locally
      for (MachineBasicBlock &MBB : MF) {
        dbgs() << MBB.getName() << "\n";
        UsedInBlk.clear();
        LiveVirtRegs.clear();
        LivePhysRegs.clear(); 
        allocateBasicBlock(MBB);
      }

      MRI->clearVirtRegs();

      return true;
    }
  };
}

/// Create the initializer and register the pass
char RegAllocSimple::ID = 0;
FunctionPass *llvm::createSimpleRegisterAllocator() { return new RegAllocSimple(); }
INITIALIZE_PASS(RegAllocSimple, "regallocsimple", "Simple Register Allocator", false, false)
static RegisterRegAlloc simpleRegAlloc("simple", "simple register allocator", createSimpleRegisterAllocator);
