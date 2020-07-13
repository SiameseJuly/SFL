#ifndef Base_H_
#define Base_H_

#include <set>

#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Pass.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/DebugInfo.h"
 
using namespace llvm;


namespace {

class Base : public ModulePass {
    public:
        char ID;
        std::set<std::string> m_blackModules;
        std::set<std::string> m_whiteModules;
        
        Base() : ModulePass(ID){
        }


    public:
        virtual ~Base();

        virtual bool runOnModule(Module &M) override = 0;

        //virtual StringRef getPassName() const override = 0;

        virtual void InitAll() =0;
        
        void initLOG(const std::string &name);

        void initBlackModules();
        
        void initWhiteModules();

        llvm::raw_ostream &LOG() const;
        
        bool checkDoing(StringRef  modulename);

        void LogLine(Instruction* Inst);
          
		//如果一个基本块被AFL的机制赋予了一个基本块ID，那么就读取出来
		bool getBBCurLoc(BasicBlock *BB, uint32_t &curLoc);

    private:
        llvm::raw_ostream *m_logFile;
    };
}

Base::~Base()
{
    if (m_logFile) {
        m_logFile->flush();
        delete m_logFile;
    }
}

void Base::initLOG(const std::string &name)
{
    std::stringstream logstream;
    logstream << "/tmp/logs/" << name << ".log";
    std::string path = logstream.str();
    
    std::error_code error;
    llvm::raw_fd_ostream *f = new llvm::raw_fd_ostream(path, error, llvm::sys::fs::F_None | llvm::sys::fs::F_Append);
    if (!f || error) {
        llvm::errs() << "Error opening " << path << ": " << error.message() << "\n";
        exit(-1); //XXX:
    }

    m_logFile = f;
}

void Base::initBlackModules()
{
    std::string blackModuleFile ="/tmp/black-white/blackModuleFile" ;
    std::ifstream blackModuleFileIO(blackModuleFile);
    std::string line;
    LOG() << "black list:\n";
    while (std::getline(blackModuleFileIO, line))
    {
        LOG() << line << "\n";
        m_blackModules.insert(line);
    }

    blackModuleFileIO.close();
}

void Base::initWhiteModules()
{
    std::string whiteModuleFile ="/tmp/black-white/whiteModuleFile" ;
    std::ifstream whiteModuleFileIO(whiteModuleFile);
    std::string line;
    while (std::getline(whiteModuleFileIO, line))
    {
        m_whiteModules.insert(line);
    }

    whiteModuleFileIO.close();
}


llvm::raw_ostream & Base::LOG() const
{
    m_logFile->flush();
    return *m_logFile;
}

// check if use our pass on this file
bool Base::checkDoing(StringRef  modulename_ref){
    
    std::string modulename = modulename_ref;
    LOG() << "CheckDoing, Running on Module " << modulename << "\n";
    //几级目录的删除XXX
    modulename.erase(modulename.begin(), modulename.begin() + modulename.rfind("/") + 1);

    //check if it in black list
     if (m_blackModules.find(modulename) != m_blackModules.end()) {
        LOG() << "find a black one "<< modulename << ", ignore this module\n";
        return false;
     }
   
    //check if it in white list
    //if (m_whiteModules.size()){
    //    LOG() << "the size of white list is " << m_whiteModules.size() << "\n";
    //    if (m_whiteModules.find(modulename) == m_whiteModules.end()) {
    //        LOG() << modulename << " not in the white list\n";
    //        return false;
    //    }
    //    LOG() << modulename << " is in the white list\n";
    //}
    //else{
    //    LOG()<<  "there is no white list, choose all the non-black  module" << "\n";
    //}
    
    LOG()<<"deal with the target module "<<modulename<<"----------------------------------------\n";
    return true;
}

// 输入行
void  Base::LogLine(Instruction* Inst){
    if (!Inst){
        LOG()<< "empty instruction\n";
        return;
    }
    if (DILocation *Loc = Inst->getDebugLoc()) {
        unsigned line = Loc->getLine();
        std::string filename = Loc->getFilename().str() ;
        LOG() << "the inst at line " << line << " in " << filename << "\n";
    }
    else{
        LOG()<< "can not get the line\n";
    }
}


//如果这个BB被插桩了，提取基本块被赋值的ID
//是不是这个不准确
bool Base::getBBCurLoc(BasicBlock *BB, uint32_t &curLoc)
{
    if (!BB){ // || BB->size() < 3) {
        //LOG() << "finding BB's cur_loc\n";
        //LOG() << "this BB too short\n";
        //LogLine( &BB->front());
        //LOG() << *BB;
        LOG() << "erro in get BB\n";
        return false;
    }

    bool findLoadPrevLoc = false;
    LoadInst *loadPrevLoc = nullptr;
    for (auto &Inst : *BB) {
        // 查找读取prev_loc的指令
        loadPrevLoc = dyn_cast<LoadInst>(&Inst);
        if (!loadPrevLoc) {
            continue;
        }

        Value *ptr = loadPrevLoc->getPointerOperand();

        if (ptr->getName().find(StringRef("__afl_prev_loc")) != std::string::npos) {
            findLoadPrevLoc = true;
            break;
        }
    }

    if (!findLoadPrevLoc) {
        LOG() << "The search block is not instrumented, continue..." << "\n";
        //LogLine( &BB->front());
        //LOG() << *BB << "\n";
        return false;
    }

    BasicBlock::iterator it = BasicBlock::iterator(loadPrevLoc); //后面的两条指令
    Instruction *_2ndInst = &(*(++it));
    Instruction *_3rdInst = &(*(++it));

    // 模式匹配
    LoadInst *loadAreaPtr = dyn_cast<LoadInst>(_2ndInst);
    Instruction *xorInst  = _3rdInst;

    if (!loadPrevLoc ||
        !loadAreaPtr ||
        !xorInst->isBinaryOp()  || 
        xorInst->getOpcode() != Instruction::Xor) {
        LOG() << "can not find the instrumented code\n";
        LogLine( &BB->front());
        LOG() << *BB << "\n";
        return false;
    }

    Value *cur_loc_value = xorInst->getOperand(1);
    ConstantInt *cur_loc = dyn_cast<ConstantInt>(cur_loc_value);
    if (!cur_loc) {
        LOG() << "can not change to a constantint\n";
        LogLine( &BB->front());
        LOG() << *BB << "\n";
        return false;
    }

    curLoc = cur_loc->getZExtValue();

    return true;
}
#endif /* ^ Base_H_ */
