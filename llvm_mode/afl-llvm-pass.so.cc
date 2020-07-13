/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
   Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

http://www.apache.org/licenses/LICENSE-2.0

This library is plugged into LLVM when invoking clang through afl-clang-fast.
It tells the compiler to add code roughly equivalent to the bits discussed
in ../afl-as.h.

*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/IR/DebugInfo.h"


using namespace llvm;

namespace {

    class AFLCoverage : public ModulePass {

        public:

            static char ID;
            AFLCoverage() : ModulePass(ID) { }

            bool runOnModule(Module &M) override;

            // StringRef getPassName() const override {
            //  return "American Fuzzy Lop InsFtrumentation";
            // }

    };

}


char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {

    LLVMContext &C = M.getContext();

    IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
    IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

    /* Show a banner */

    char be_quiet = 0;
    if (isatty(2) && !getenv("AFL_QUIET")) {

        SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

    } else be_quiet = 1;

    /* Decide instrumentation ratio */

    char* inst_ratio_str = getenv("AFL_INST_RATIO");
    unsigned int inst_ratio = 100;

    if (inst_ratio_str) {

        if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
                inst_ratio > 100)
            FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");
    }

    /* Get globals for the SHM region and the previous location. Note that
       __afl_prev_loc is thread-local. */

    GlobalVariable *AFLMapPtr =
        new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

    GlobalVariable *AFLPrevLoc = new GlobalVariable(
            M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
            0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

    /* struct-afl pass  */
    /* case_map[128] */
    GlobalVariable *SFLMapPtr = new GlobalVariable(M, PointerType::get(Int8Ty, 0),false,GlobalVariable::ExternalLinkage, 0, "__sfl_case_ptr");

    /* sequence[128] */
    GlobalVariable *SFLSequnce = new GlobalVariable(M, PointerType::get(Int8Ty, 0),false, GlobalVariable::ExternalLinkage, 0, "__sfl_sequence");

    /* sequence length */
    GlobalVariable *SFLSeqLength = new GlobalVariable(M, Int8Ty,false, GlobalVariable::ExternalLinkage, 0, "__sfl_length");
    GlobalVariable *SFLSeqLengthPtr = new GlobalVariable(M,  PointerType::get(Int8Ty, 0),false, GlobalVariable::ExternalLinkage, 0, "__sfl_length_ptr");
    /* Instrument all the things! */

    int inst_blocks = 0;
    int inst_switch = 1;

    for (auto &F : M)
        for(auto &BB : F) {
            /* get first instruction in a baisc block */

            const Instruction *FirstIns = BB.getFirstNonPHI();
            DILocation *Loc = FirstIns->getDebugLoc();
            if(!Loc){
                continue;
            }
            unsigned Line = 0;
            std::string Filename;
            Line = Loc->getLine();
            Filename = Loc->getFilename();
            //std::string aim_file = "src/bin.c";
            //std::string aim_file = "tiff2pdf.c";
            std::string aim_file = "exif.c";
            //std::string aim_file = "bin.c";
            //std::string aim_file = "test-instr.c";
            //std::string aim_file = "/home/siamese/struct-state-fuzz/env/cb-multios/challenges/Modern_Family_Tree/src/service.c";
            if (Filename != aim_file){

                SAYF("Now is in file:: %s ,but we aim file::%s\n",Filename.c_str(),aim_file.c_str());
                continue;
            }

            //if (Line < 44 || Line > 62 ){
            //if (Line < 44 || Line > 61){  //bctf06
            //if (Line < 45 || Line > 60){
            //if (Line < 841 || Line > 855){
            //if (Line < 39 || Line > 58){    //bctf07
            //if (Line < 3468 || Line > 3578){ //tiff2pdf
            if (Line < 1576 || Line > 1607){ //php_exif   
            continue;
            }
            SAYF("Now is in aim::File %s Line %d \n",Filename.c_str(),Line);
            BasicBlock::iterator IP = BB.getFirstInsertionPt();
            IRBuilder<> IRB(&(*IP));

            /* Make up case Hash 
             * Here we hard-code by index
             * */

            unsigned int case_id = inst_switch;


            ConstantInt *CaseId = ConstantInt::get(Int8Ty, case_id);

            /* Update SFL casemap */
            /* First, make up pointer casemap[0]*/

            LoadInst *CaseMapPtr = IRB.CreateLoad(SFLMapPtr);
            CaseMapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            Value *CaseMapIdx = IRB.CreateGEP(CaseMapPtr, IRB.CreateAdd(CaseId, ConstantInt::get(Int8Ty, 0)));

            /* Second, get the value of casemap[id] */

            LoadInst *CaseCounter = IRB.CreateLoad(CaseMapIdx);
            CaseCounter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

            /* third, casemap[id] += 1*/
            Value *CaseMapIncr = IRB.CreateAdd(CaseCounter, ConstantInt::get(Int8Ty, 1));
            //Value *CaseMapIncr = IRB.CreateAdd(CaseCounter, ConstantInt::get(Int8Ty, 1));
            IRB.CreateStore(CaseMapIncr, CaseMapIdx)
                ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

            /* Update sequence[128] */
            /* First, make up pointer sequence*/
            LoadInst *SeqPtr = IRB.CreateLoad(SFLSequnce);
            SeqPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

            /* Second, get length of sequence*/
            LoadInst *SeqLength = IRB.CreateLoad(SFLSeqLength);
            SeqLength->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            //Value *SeqLengthPre  = IRB.CreateZExt(SeqLength, IRB.getInt32Ty());
            /* update sequence */
            Value *SeqIdx = IRB.CreateGEP(SeqPtr, SeqLength);
            IRB.CreateStore(CaseId, SeqIdx)
                ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

            LoadInst *SeqLengthPtr = IRB.CreateLoad(SFLSeqLengthPtr);
            SeqLengthPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            /* Update sequence length*/
            Value *UpdateSeqLength = IRB.CreateAdd(SeqLength, ConstantInt::get(Int8Ty, 1));
            //Value *UpdateSeqLength = IRB.CreateAdd(SeqLength, ConstantInt::get(Int8Ty, 1));
            IRB.CreateStore(UpdateSeqLength, SFLSeqLength)
                ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

            inst_switch++;
        }
    
    for (auto &F:M)
        for (auto &BB : F) {

            BasicBlock::iterator IP = BB.getFirstInsertionPt();
            IRBuilder<> IRB(&(*IP));

            if (AFL_R(100) >= inst_ratio) continue;

            /* Make up cur_loc */

            unsigned int cur_loc = AFL_R(MAP_SIZE);

            ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

            /* Load prev_loc */

            LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
            PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

            /* Load SHM pointer */

            LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
            MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            Value *MapPtrIdx =
                IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

            /* Update bitmap */

            LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
            Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
            IRB.CreateStore(Incr, MapPtrIdx)
                ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

            /* Set prev_loc to cur_loc >> 1 */

            StoreInst *Store =
                IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
            Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

            inst_blocks++;

        }

    /* Say something nice. */

    if (!be_quiet) {

        if (!inst_blocks) WARNF("No instrumentation targets found.");
        else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
                inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
                ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
                 "ASAN/MSAN" : "non-hardened"), inst_ratio);

    }

    return true;

}


static void registerAFLPass(const PassManagerBuilder &,
        legacy::PassManagerBase &PM) {

    PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
        PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
        PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
