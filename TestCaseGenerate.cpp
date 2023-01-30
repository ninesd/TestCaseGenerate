#include "clang/Driver/Options.h"
#include "clang/AST/AST.h"
#include "clang/AST/Type.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Rewrite/Core/Rewriter.h"

#include <vector>
#include <string>
#include <iostream>
#include <unordered_set>
#include <set>
#include <map>
#include <stdio.h>
#include <boost/filesystem.hpp>
#include <boost/filesystem/fstream.hpp>
#include <boost/regex.hpp>
#include <sys/time.h>

#define CLANG_VERSION 9

#if CLANG_VERSION > 3
#define TRIGGER
#endif

using namespace std;
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace llvm;
namespace fs = boost::filesystem;

// 目标函数相关
vector<FunctionDecl*> funcDeclList;
FunctionDecl *targetFuncDecl;
FunctionDecl *mainFuncDecl;
bool hasMain;
SourceLocation targetFuncStartLoc;
SourceLocation targetFuncEndLoc;

// message.txt内容
string messageStr = "";

// 需要符号化的变量（函数参数、全局变量）
set<string> vars;

// 变量类型打印策略
LangOptions langOptions;
PrintingPolicy printingPolicy(langOptions);

// 变量符号化代码文本
string makeSymbolicStmt;

// 输出文件夹名
string resultDirStr;

// 文件路径
string pathString, preprocessedPathString;

// 测试用例序列编号与真值与文本的相关信息，用于从生成的MCC测试用例中挑选需要的测试用例
vector<map<unsigned int, pair<long long, long long> > > trueSeqNum2ExpectList;
vector<map<unsigned int, pair<long long, long long> > > falseSeqNum2ExpectList;
vector<map<pair<long long, long long>, unsigned int> > expect2SeqNumList;
vector<vector<string> > conditionTextList;
vector<string> decisionTextList;

// 记录所有真值表的数量
int MCDCGen, MCDCAll, CDCGen, CDCAll, conditionGen, conditionAll, decisionGen, decisionAll, MCCGen, MCCAll, SwitchGen, SwitchAll;
int caseNumMCDC, caseNumMCC, caseNumCondition, caseNumDecision, caseNumCDC;
int KMCDCGen, KMCDCAll, KCDCGen, KCDCAll, KconditionGen, KconditionAll, KdecisionGen, KdecisionAll, KMCCGen, KMCCAll, KSwitchGen, KSwitchAll;

// 当前TriggerNum
int triggerNum;
vector<int> triggerNumSet;

// 记录找到的所有extern变量
set<VarDecl*> externVariables;

int EnableSpecPath = 0;
vector<vector<int> > specifiedPath;
vector<vector<int> > switchPath;
int pathCount = 0;
int specifiedPathCount = 0;
int switchPathCount = 0;

// buffer数组的最大长度
#define MAX_BUFFER_SIZE 10240

#define INDENTATION_NUM 4

string KappaSubDirNameStr = "kappa";


// 表示操作符类型，其中not可与其他操作符混用，表示对运作结果做非运算
// 0b1000
#define NOT 8
// 0b0100
#define XOR 4
// 0b0010
#define AND 2
// 0b0001
#define OR 1

static cl::OptionCategory TCGCategory("TCG options");

cl::opt<bool> KleePrintMode("klee-print", cl::desc("Klee Print Mode (default=false)."), cl::init(false));
cl::opt<bool> OrigKleeMode("orig-klee", cl::desc("Orig Klee Mode (default=false)."), cl::init(false));
cl::opt<bool> OrigKleeCov("orig-cov", cl::desc("Output Orig Klee Coverage (default=false)."), cl::init(false));

cl::opt<string> MaxTime("max-time", cl::desc("Max KLEE run time."), cl::init(""));
cl::opt<string> MaxMemory("max-memory", cl::desc("Max KLEE run memory."), cl::init(""));

cl::opt<bool> conditionCoverageOutput("condition", cl::desc("create condition coverage output file (default=false)."), cl::init(false));
cl::opt<bool> decisionCoverageOutput("decision", cl::desc("create decision coverage output file (default=false)."), cl::init(false));
cl::opt<bool> CDCOutput("CDC", cl::desc("create CDC output file (default=false)."), cl::init(false));
cl::opt<bool> MCCOutput("MCC", cl::desc("create MCC output file (default=false)."), cl::init(false));
cl::opt<bool> MCDCOutput("MCDC", cl::desc("create MCDC output file (default=false)."), cl::init(false));
cl::opt<bool> statementCoverageOutput("statement", cl::desc("create statement coverage output file (default=false)."), cl::init(false));
cl::opt<bool> pathCoverageOutput("path", cl::desc("create path coverage output file (default=false)."), cl::init(false));

cl::opt<bool> addInclude("addI", cl::desc("add klee include at the start of the file (default=true)."), cl::init(true));
cl::opt<bool> addDriverFunc("addD", cl::desc("add parameter definition, klee symbolic definition and function call at the start of main function (default=true)."), cl::init(true));
cl::opt<string> targetFuncName("func", cl::desc("function to be tested (default=main)."), cl::init("main"));
cl::opt<bool> runKlee("runKlee", cl::desc("run klee after source2source transform (default=true)."), cl::init(true));
cl::opt<bool> DEBUG("DEBUG", cl::desc("output debug message (default=false)."), cl::init(false));
cl::opt<bool> EmitAllErrors("emit-all-errors", cl::desc("generate tests cases for all errors (default=false)."), cl::init(false));
cl::opt<int> boundary("boundary", cl::desc("Upper Bound and Lower Bound of INT value (default=-1, unbounded)."), cl::init(-1));
cl::opt<string> KleePath("klee-path", cl::desc("Path of klee"), cl::init("klee"));
cl::opt<string> KleeIncludePath("klee-include-path", cl::desc("Path of klee include dir"), cl::init(""));
cl::opt<string> ClangPath("clang-path", cl::desc("Path of clang"), cl::init("clang"));
cl::opt<string> Searcher("searcher", cl::desc("Searcher (default=dfs)."), cl::init(""));
cl::opt<bool> EnableMerge("use-merge", cl::desc("Use KLEE merge (default=false)."), cl::init(false));
cl::opt<bool> AddIndentation("indentation", cl::desc("Add Indentation (default=true)."), cl::init(true));
cl::opt<bool> GlobalVarSym("global-var-sym", cl::desc("Make global variable symbolic (default=true)."), cl::init(true));
cl::opt<bool> GenForAllFunc("all-func", cl::desc("Generate kappa stmt for all function (default=false)."), cl::init(false));
cl::opt<bool> GenForAllFuncExpectMain("all-func-expect-main", cl::desc("Generate kappa stmt for all function expect main (default=false)."), cl::init(false));
cl::opt<bool> EarlyStop("early-stop", cl::desc("In decision Mode, Terminate state when reach assert stmt (default=false)."), cl::init(false));
cl::opt<bool> Optimize("optimize", cl::desc("Enable klee optimize (default=true)."), cl::init(true));

cl::opt<string> SpecPath("specPath", cl::desc("Specify path."), cl::init(""));

cl::opt<bool> IgnorePrintf("ignore-printf", cl::desc("Ignore Printf (default=false)."), cl::init(false));

cl::opt<int> MaxLoopTimes("max-loop-times", cl::desc("Only fork this many times in loop (default=disable)."), cl::init(-1));
cl::opt<int> MaxLoopForkTimes("max-loop-fork-times", cl::desc("Only loop this many times (default=disable)."), cl::init(-1));
cl::list<string> LinkLib("link-llvm-lib", cl::desc("Link LLVM Lib .a .bc .so.bc (default=disable)."));


enum class ClangOptimizationOption {
    O_,
    O0,
    O1,
    O2,
    O3,
    Ofast
};
cl::opt<ClangOptimizationOption> ClangOpt(
        "opt", cl::desc("Clang optimization option (default=true)."),
        cl::values(
                clEnumValN(ClangOptimizationOption::O_, "O-", "without any optimization"),
                clEnumValN(ClangOptimizationOption::O0, "O0", "O0"),
                clEnumValN(ClangOptimizationOption::O1, "O1", "O1"),
                clEnumValN(ClangOptimizationOption::O2, "O2", "O2"),
                clEnumValN(ClangOptimizationOption::O3, "O3", "O3"),
                clEnumValN(ClangOptimizationOption::Ofast, "Ofast", "Ofast")
#if CLANG_VERSION == 3
                ,clEnumValEnd),
#else
        ),
#endif
        cl::init(ClangOptimizationOption::O_));

enum class SearchPolicy {
    Auto,
    Search,
    Greedy,
};

cl::opt<SearchPolicy> SearchMode(
        "search-mode",
        cl::desc("Specify the search policy (default=auto)."),
        cl::values(
                clEnumValN(SearchPolicy::Auto, "auto", "Switch between Search and Greedy depend on the input size"),
                clEnumValN(SearchPolicy::Search, "search", "Always Search"),
                clEnumValN(SearchPolicy::Greedy, "greedy", "Always Greedy")
#if CLANG_VERSION == 3
                ,clEnumValEnd),
#else
        ),
#endif
        cl::init(SearchPolicy::Auto));


enum class KappaGeneratePolicy {
    All,
    Decision,
    Sequence,
};

cl::opt<KappaGeneratePolicy> KappaMode(
        "kappa-mode",
        cl::desc("Specify the Kappa generate policy (default=d)."),
        cl::values(
                clEnumValN(KappaGeneratePolicy::All, "a", "generate all sequences in one file"),
                clEnumValN(KappaGeneratePolicy::Decision, "d", "generate each decision one file"),
                clEnumValN(KappaGeneratePolicy::Sequence, "s", "generate each sequence one file")
#if CLANG_VERSION == 3
                ,clEnumValEnd),
#else
        ),
#endif
        cl::init(KappaGeneratePolicy::Decision));


enum class TracerXPolicy {
    On,
    Off,
    Default,
};

cl::opt<TracerXPolicy> TracerX(
        "tracerx",
        cl::desc("Specify the TracerX policy (default=default)."),
        cl::values(
                clEnumValN(TracerXPolicy::On, "on", "generate all sequences in one file"),
                clEnumValN(TracerXPolicy::Off, "off", "generate each decision one file"),
                clEnumValN(TracerXPolicy::Default, "default", "generate each decision one file")
#if CLANG_VERSION == 3
                ,clEnumValEnd),
#else
        ),
#endif
        cl::init(TracerXPolicy::Default));


// 将src中的全部内容添加到dest中
void addAll(vector<pair<long long, long long> > &dest, vector<pair<long long, long long> > &src) {
    dest.insert(dest.end(), src.begin(), src.end());
}

string formatDoubleValue(double val, int fixed) {
    string str = std::to_string(val);
    return str.substr(0, str.find(".") + fixed + 1);
}

string replaceStr(string str, string from="\n", string to=" ") {
    string::size_type pos;
    do {
        pos = str.find(from);
        if (pos != string::npos) {
            str.replace(pos, from.size(), to);
        }
    } while (pos != string::npos);
    return str;
}

string replaceEnterInStr(string str) {
    string::size_type from;
    do {
        // 找到文本中换行符出现的位置
        from = str.find("\n");
        if (from != string::npos) {
            string::size_type pos;
            // 从换行符开始，标记所有连续空白符
            for (pos = from; pos<str.size(); pos++)
                if (str.at(pos)!='\n' && str.at(pos)!=' ' && str.at(pos)!='\t') break;
            // 若换行符前没有空白符，添加空格
            if (from!=0 && str.at(from-1)!=' ' && str.at(from-1)!='\t')
                str.replace(from, pos-from, " ");
            else
                str.replace(from, pos-from, "");
        }
    } while (from != string::npos);
    return str;
}


// 继承Rewriter类，添加对宏的处理
class CustomRewriter final : public Rewriter {
public:
    explicit CustomRewriter() = default;
    explicit CustomRewriter(SourceManager &SM, const LangOptions &LO) : Rewriter(SM, LO) {}

    bool ReplaceText(SourceRange range, StringRef NewStr) {
        SourceLocation startLoc = range.getBegin();
        SourceLocation endLoc = range.getEnd();

        if (startLoc.isMacroID()) {
            startLoc = Rewriter::getSourceMgr().getExpansionLoc(startLoc);
            range = SourceRange(startLoc, endLoc);
        }

        if (endLoc.isMacroID()) {
            endLoc = Rewriter::getSourceMgr().getExpansionLoc(endLoc);
            range = SourceRange(startLoc, endLoc);
        }

        return Rewriter::ReplaceText(range, NewStr);
    }

    string getRewrittenText(SourceRange range) {
        SourceLocation startLoc = range.getBegin();
        SourceLocation endLoc = range.getEnd();

        if (startLoc.isMacroID()) {
            startLoc = Rewriter::getSourceMgr().getExpansionLoc(startLoc);
            range = SourceRange(startLoc, endLoc);
        }

        if (endLoc.isMacroID()) {
            endLoc = Rewriter::getSourceMgr().getExpansionLoc(endLoc);
            range = SourceRange(startLoc, endLoc);
        }

        return Rewriter::getRewrittenText(range);
    }
};

// 用于提取未经修改的源代码文本
CustomRewriter sourceCode;

// 从给定的test case序列中选择满足覆盖率的test case集合
class TestCaseSelector {
private:
    vector<pair<long long, long long> > trueCases;
    vector<pair<long long, long long> > falseCases;
    vector<pair<long long, long long> > allCases;
    vector<string> conditions;
    string decision;
    vector<string> testCaseFileNameList;
    bool afterKlee;
    bool origKlee;
    unsigned int conditionNum;
    int truthTableSeqCnt;

    // 返回测试用例真值表
    string printCases(set<unsigned int> selected) {
        string truthTable = "| ";
        string separation;
        int cnt = 0;

        for (string conditionText : conditions) {
            truthTable += conditionText;
            // 对齐，使输出更易于查看
            truthTable += " | ";
        }
        truthTable += "out |\n| ";

        for (unsigned int i=0; i<allCases.size(); i++) {
            if (selected.count(i)==0) continue;
            cnt++;
            pair<long long, long long> row = allCases.at(i);
            for (unsigned int j=0; j<conditionNum; j++) {
                separation = "";
                int conditionStrLen = conditions.at(j).length() - 1;
                while (conditionStrLen >= 0) {
                    separation += " ";
                    conditionStrLen--;
                }
                separation += "| ";

                if (!(row.second & 1LL<<j)) truthTable += "X" + separation;
                else if (row.first & 1LL<<j) truthTable += "T" + separation;
                else truthTable += "F" + separation;
            }
            if (i < trueCases.size())
                truthTable += "T   |";
            else
                truthTable += "F   |";
            if (testCaseFileNameList.empty())
                truthTable += "\n| ";
            else
                truthTable += "   "+testCaseFileNameList.at(i)+"    "+ to_string(allCases.at(i).first)+"\n| ";
        }
        truthTable = truthTable.substr(0, truthTable.size()-3);
        llvm::errs() << truthTable << "\n";
        llvm::errs() << "generate " << to_string(cnt) << " cases!\n";

        if (!testCaseFileNameList.empty()) {
            messageStr += truthTable+"\n"+"generate "+to_string(cnt)+" cases!\n";
        }

        return truthTable;
    }

    // 返回真值表
    string printCases() {
        set<unsigned int> result;
        for (unsigned int i=0; i<allCases.size(); i++)
            result.insert(i);
        return printCases(result);
    }


    // 是否可以被剪枝
    bool ifNotCovered(set<long long> &oldState, long long currentState) {
        for (auto itState = oldState.begin(); itState != oldState.end(); ) {
            if ((*itState | currentState) == *itState) {
                return false;
            }
            else if ((*itState | currentState) == currentState) {
                itState = oldState.erase(itState);
            }
            else {
                itState++;
            }
        }
        oldState.insert(currentState);
        return true;
    }

    // 广搜求最小组合 for condition / CDC
    // 从seqs中取出若干seq, 或运算, 求使结果到达target的数量最小的seq组合
    set<unsigned int> bfsCondition(vector<long long> &seqs, long long target) {
        // visited表示过去途经的状态
        unordered_set<long long> visited;
        // oldState表示当前存储的状态集（互不重合） 用于加速
        set<long long> oldState;
        // queue表示广搜队列
        vector<pair<long long, unsigned int> > queue;
        // prior维护queue中每一项的前一项下标, 用于最后输出
        vector<unsigned int> prior;
        set<unsigned int> result;
        queue.reserve(1000000);
        prior.reserve(1000000);

        unsigned int head = 0;
        queue.push_back(make_pair(0, 0));
        visited.insert(0);
        oldState.insert(0);

        while (head!=queue.size()) {
            for (unsigned int i=0; i<seqs.size(); i++) {
                long long newState = seqs.at(i) | queue.at(head).first;
                // 到达target
                if (newState == target) {
                    result.insert(i);
                    int cur = head;
                    while (cur != 0) {
                        result.insert(queue.at(cur).second);
                        cur = prior.at(cur);
                    }
                    return result;
                }

                if (visited.count(newState)==0) {
                    visited.insert(newState);
                    if (ifNotCovered(oldState, newState)) {
                        queue.push_back(make_pair(newState, i));
                        prior.push_back(head);
                    }
                }
            }
            head++;
        }

        return result;
    }

    // 贪心求下一步最优选择
    int selectNextMostLikely(vector<long long> &seqs, long long currentState) {
        int idx=-1, maxNum = 0;
        for (unsigned int i=0; i<seqs.size(); i++) {
            long long update = (~currentState) & seqs.at(i);
            int num = 0;
            while (update) {
                if (update & 1) num++;
                update >>= 1;
            }
            if (num > maxNum) {
                idx = i;
                maxNum = num;
            }
        }
        return idx;
    }

    // 贪心求最小组合 for condition / CDC
    set<unsigned int> greedyCondition(vector<long long> &seqs, long long target) {
        long long currentState = 0;
        set<unsigned int> result;
        while (currentState != target) {
            int selected = selectNextMostLikely(seqs, currentState);
            // 无法到达100%覆盖率，退出
            if (selected==-1) break;
            result.insert(selected);
            currentState |= seqs.at(selected);
        }
        return result;
    }

    // 贪心求MCDC
    set<unsigned int> greedyMCDC(vector<vector<pair<unsigned int, unsigned int> > > &MCDCPairs) {
        set<unsigned int> selectedSeq;

        for (int i=0; i<MCDCPairs.size(); i++) {
            bool continueFlag = true;
            for (pair<unsigned int, unsigned int> item : MCDCPairs.at(i)) {
                if (selectedSeq.count(item.first) && selectedSeq.count(item.second)) {
                    continueFlag = false;
                    break;
                }
            }
            if (!continueFlag) continue;

            for (pair<unsigned int, unsigned int> item : MCDCPairs.at(i)) {
                if (selectedSeq.count(item.first)) {
                    selectedSeq.insert(item.second);
                    continueFlag = false;
                    break;
                }
                else
                if (selectedSeq.count(item.second)) {
                    selectedSeq.insert(item.first);
                    continueFlag = false;
                    break;
                }
            }
            if (!continueFlag) continue;
            for (pair<unsigned int, unsigned int> item : MCDCPairs.at(i)) {
                selectedSeq.insert(item.first);
                selectedSeq.insert(item.second);
                continueFlag = false;
                break;
            }
        }

        return selectedSeq;
    }

    set<unsigned int> bestMCDCResult;
    unsigned int best;
    int mcdcTryTimes;

    // dfs求MCDC 递归过程
    void rdfsMCDC(vector<vector<pair<unsigned int, unsigned int> > > &MCDCPairs,
    unsigned int conditionIdx, map<unsigned int, bool> &selectedSeq, int selectedNum) {
        if (mcdcTryTimes > 1000000) {
            return;
        }
        mcdcTryTimes++;

        if (selectedNum >= best) return;

        if (conditionIdx >= MCDCPairs.size()) {
            bestMCDCResult.clear();
            best = selectedNum;
            for (auto i : selectedSeq) {
                if (i.second)
                    bestMCDCResult.insert(i.first);
            }
            return;
        }

        if (MCDCPairs.at(conditionIdx).empty()) {
            rdfsMCDC(MCDCPairs, conditionIdx+1, selectedSeq, selectedNum);
            return;
        }

        for (pair<unsigned int, unsigned int> item : MCDCPairs.at(conditionIdx)) {
            if (selectedSeq.count(item.first) && selectedSeq.at(item.first) && selectedSeq.count(item.second) && selectedSeq.at(item.second)) {
                rdfsMCDC(MCDCPairs, conditionIdx+1, selectedSeq, selectedNum);
                return;
            }
        }

        for (pair<unsigned int, unsigned int> item : MCDCPairs.at(conditionIdx)) {
            if (selectedSeq.count(item.first) && selectedSeq.at(item.first)) {
                if (selectedSeq.count(item.second))
                    selectedSeq.at(item.second) = true;
                else
                    selectedSeq.insert(make_pair(item.second, true));
                rdfsMCDC(MCDCPairs, conditionIdx+1, selectedSeq, selectedNum+1);
                selectedSeq.at(item.second) = false;
            }
            else if (selectedSeq.count(item.second) && selectedSeq.at(item.second)) {
                if (selectedSeq.count(item.first))
                    selectedSeq.at(item.first) = true;
                else
                    selectedSeq.insert(make_pair(item.first, true));
                rdfsMCDC(MCDCPairs, conditionIdx+1, selectedSeq, selectedNum+1);
                selectedSeq.at(item.first) = false;
            }
            else {
                if (selectedSeq.count(item.second))
                    selectedSeq.at(item.second) = true;
                else
                    selectedSeq.insert(make_pair(item.second, true));
                if (selectedSeq.count(item.first))
                    selectedSeq.at(item.first) = true;
                else
                    selectedSeq.insert(make_pair(item.first, true));
                rdfsMCDC(MCDCPairs, conditionIdx+1, selectedSeq, selectedNum+2);
                selectedSeq.at(item.first) = false;
                selectedSeq.at(item.second) = false;
            }
        }
    }

    // dfs求MCDC 初始化
    set<unsigned int> dfsMCDC(vector<vector<pair<unsigned int, unsigned int> > > &MCDCPairs) {
        bestMCDCResult.clear();
        set<unsigned int> result;
        result = greedyMCDC(MCDCPairs);
        best = result.size();
        int tmp = best;
        map<unsigned int, bool> selectedSeq;
        mcdcTryTimes = 0;
        rdfsMCDC(MCDCPairs, 0, selectedSeq, 0);

        if (best < tmp) {
            result.clear();
            for (unsigned int i : bestMCDCResult) {
                result.insert(i);
            }
        }

        return result;
    }


    // 计算decision coverage
    vector<pair<long long, long long> > calculateDecision() {
        vector<pair<long long, long long> > decisionResult;
        set<unsigned int> result;
        if (!trueCases.empty()) {
            decisionResult.push_back(trueCases.at(0));
            result.insert(0);
        }
        if (!falseCases.empty()) {
            decisionResult.push_back(falseCases.at(0));
            result.insert(trueCases.size());
        }

        if (!result.empty()) {
            llvm::errs() << "\nDecision coverage result is :\n";
            if (afterKlee) messageStr += "\nDecision coverage result is :\n";
            printCases(result);
        }
        else {
            llvm::errs() << "\nGenerate 0 Decision test case!\n";
            if (afterKlee) messageStr += "\nGenerate 0 Decision test case!\n";
        }

        if (afterKlee) {
            llvm::errs() << "Decision coverage : " << formatDoubleValue((double)result.size()*100/2, 2) << "%\n\n";
            messageStr += "Decision coverage : "+formatDoubleValue((double)result.size()*100/2, 2)+"%\n\n";
            decisionGen += result.size();
            decisionAll += 2;
        }
        if (origKlee) {
            KdecisionGen += result.size();
            KdecisionAll += 2;
        }
        return decisionResult;
    }

    // 计算condition coverage
    vector<pair<long long, long long> > calculateCondition() {
        // 转换为使用两位表示一位bool，T/F分开
        vector<long long> seqs;
        for (pair<long long, long long> seq : allCases) {
            long long bitmap = 0;
            for (unsigned int i=0; i<conditionNum; i++) {
                if (((seq.first & 1L<<i)!=0) && (seq.second & 1L<<i)) bitmap |= 1L<<(i*2);
                if (((seq.first & 1L<<i)==0) && (seq.second & 1L<<i)) bitmap |= 1L<<(i*2+1);
            }
            seqs.push_back(bitmap);
        }

        set<unsigned int> result;
        long long target = 0;
        for (long long seq : seqs) target |= seq;
        if (SearchMode == SearchPolicy::Search)
            result = bfsCondition(seqs, target);
        else if (SearchMode == SearchPolicy::Greedy)
            result = greedyCondition(seqs, target);
        else {
            if (seqs.size() <= 200)
                result = bfsCondition(seqs, target);
            else
                result = greedyCondition(seqs, target);
        }

        vector<pair<long long, long long> > conditionResult;
        if (!result.empty()) {
            for (unsigned int item : result) {
                conditionResult.push_back(allCases.at(item));
            }
        }

        if (!result.empty()) {
            llvm::errs() << "\nCondition coverage result is :\n";
            if (afterKlee) messageStr += "\nCondition coverage result is :\n";
            printCases(result);
        }
        else {
            llvm::errs() << "\nGenerate 0 Condition test case!\n";
            if (afterKlee) messageStr += "\nGenerate 0 Condition test case!\n";
        }

        int completeConditionNum = 0;
        long long tmp = target;
        while (tmp) {
            if (tmp & 1) completeConditionNum++;
            tmp >>= 1;
        }
        if (afterKlee) {
            llvm::errs() << "Condition coverage : " << formatDoubleValue((double)completeConditionNum*100/(conditionNum*2), 2) << "%\n\n";
            messageStr += "Condition coverage : "+formatDoubleValue((double)completeConditionNum*100/(conditionNum*2), 2)+"%\n\n";
            conditionGen += completeConditionNum;
            conditionAll += conditionNum*2;
        }
        if (origKlee) {
            KconditionGen += completeConditionNum;
            KconditionAll += conditionNum*2;
        }

        return conditionResult;
    }

    // 计算CDC
    vector<pair<long long, long long> > calculateCDC() {
        // 转换为使用两位表示一位bool，T/F分开
        vector<long long> seqs;
        for (unsigned int j=0; j<allCases.size(); j++) {
            pair<long long, long long> seq = allCases.at(j);
            long long bitmap = 0;
            for (unsigned int i=0; i<conditionNum; i++) {
                if (((seq.first & 1L<<i)!=0) && (seq.second & 1L<<i)) bitmap |= 1L<<(i*2);
                if (((seq.first & 1L<<i)==0) && (seq.second & 1L<<i)) bitmap |= 1L<<(i*2+1);
            }
            if (j<trueCases.size())
                bitmap |= 1L<<(conditionNum*2);
            else
                bitmap |= 1L<<(conditionNum*2+1);
            seqs.push_back(bitmap);
        }

        set<unsigned int> result;
        long long target = 0;
        for (long long seq : seqs) target |= seq;
        if (SearchMode == SearchPolicy::Search)
            result = bfsCondition(seqs, target);
        else if (SearchMode == SearchPolicy::Greedy)
            result = greedyCondition(seqs, target);
        else {
            if (seqs.size() <= 200)
                result = bfsCondition(seqs, target);
            else
                result = greedyCondition(seqs, target);
        }

        vector<pair<long long, long long> > CDCResult;
        if (!result.empty()) {
            for (unsigned int item : result) {
                CDCResult.push_back(allCases.at(item));
            }
        }

        if (!result.empty()) {
            llvm::errs() << "\nCDC result is :\n";
            if (afterKlee) messageStr += "\nCDC result is :\n";
            printCases(result);
        }
        else {
            llvm::errs() << "Generate 0 CDC test case!\n";
            if (afterKlee) messageStr += "\nGenerate 0 CDC test case!\n";
        }

        int completeConditionNum = 0;
        long long tmp = target;
        while (tmp) {
            if (tmp & 1) completeConditionNum++;
            tmp >>= 1;
        }
        if (afterKlee) {
            llvm::errs() << "CDC : " << formatDoubleValue((double)completeConditionNum*100/(conditionNum*2+2), 2) << "%\n\n";
            messageStr += "CDC : "+formatDoubleValue((double)completeConditionNum*100/(conditionNum*2+2), 2)+"%\n\n";
            CDCGen += completeConditionNum;
            CDCAll += conditionNum*2+2;
        }
        if (origKlee) {
            KCDCGen += completeConditionNum;
            KCDCAll += conditionNum*2+2;
        }

        return CDCResult;
    }

    // 计算MCDC
    vector<pair<long long, long long> > calculateMCDC() {
        vector<vector<pair<unsigned int, unsigned int> > > MCDCPairs;
        vector<vector<pair<unsigned int, unsigned int> > > MaskingPairs;
        int completePairNum = 0;
        for (unsigned int i=0; i<conditionNum; i++) {
            MCDCPairs.push_back(vector<pair<unsigned int, unsigned int> >());
            MaskingPairs.push_back(vector<pair<unsigned int, unsigned int> >());
        }
        for (unsigned int i=0; i<trueCases.size(); i++) {
            for (unsigned int j=0; j<falseCases.size(); j++) {
                pair<long long, long long> seq1 = trueCases.at(i);
                pair<long long, long long> seq2 = falseCases.at(j);
                for (unsigned int k=0; k<conditionNum; k++) {
                    long long target = 1LL<<k;
                    if (((seq1.second & target)!=0) && ((seq2.second & target)!=0)
                        && ((seq1.first & target) != (seq2.first & target))) {
                        MaskingPairs.at(k).push_back(make_pair(i, j+trueCases.size()));
                        long long diff = (seq1.first ^ seq2.first) & (seq1.second & seq2.second);
                        if (diff==0 || diff==target) {
                            MCDCPairs.at(k).push_back(make_pair(i, j+trueCases.size()));
                        }
                    }
                }
            }
        }
        for (unsigned int i=0; i<conditionNum; i++) {
            if (MCDCPairs.at(i).empty() && !origKlee)
                MCDCPairs.at(i).insert(MCDCPairs.at(i).end(), MaskingPairs.at(i).begin(), MaskingPairs.at(i).end());
            // 检查给定的测试用例集能否得到100%的MCDC
            if (!MCDCPairs.at(i).empty())
                completePairNum++;
        }

        set<unsigned int> result;
        if (SearchMode == SearchPolicy::Search)
            result = dfsMCDC(MCDCPairs);
        else if (SearchMode == SearchPolicy::Search)
            result = greedyMCDC(MCDCPairs);
        else {
            if (allCases.size() > 80)
                result = greedyMCDC(MCDCPairs);
            else
                result = dfsMCDC(MCDCPairs);
        }

        vector<pair<long long, long long> > MCDCResult;
        if (!result.empty()) {
            for (unsigned int item : result) {
                MCDCResult.push_back(allCases.at(item));
            }
        }

        if (!result.empty()) {
            llvm::errs() << "\nMCDC result is :\n";
            if (afterKlee) messageStr += "\nMCDC result is :\n";
            printCases(result);
        }
        else {
            llvm::errs() << "Generate 0 MCDC test case!\n";
            if (afterKlee) messageStr += "\nGenerate 0 MCDC test case!\n";
        }

        if (afterKlee) {
            llvm::errs() << "MCDC : " << formatDoubleValue((double)completePairNum*100/conditionNum, 2) << "%\n\n";
            messageStr += "MCDC : "+formatDoubleValue((double)completePairNum*100/conditionNum, 2)+"%\n\n";
            MCDCGen += completePairNum;
            MCDCAll += conditionNum;
        }
        if (origKlee) {
            KMCDCGen += completePairNum;
            KMCDCAll += conditionNum;
        }

        return MCDCResult;
    }

public:
    vector<pair<long long, long long> > conditionTestCases;
    vector<pair<long long, long long> > decisionTestCases;
    vector<pair<long long, long long> > CDCTestCases;
    vector<pair<long long, long long> > MCCTestCases;
    vector<pair<long long, long long> > MCDCTestCases;

    // 通过给定测试用例自动挑选出满足某覆盖率所需的测试用例
    // conditions表示该decision的condition文本, truthTableSeqCnt表示该decision的真值表条目数量
    TestCaseSelector(vector<pair<long long, long long> > &trueCases,
                     vector<pair<long long, long long> > &falseCases,
                     vector<string> &conditions,
                     string decision,
                     vector<string> testCaseFileNameList = vector<string>(),
                     bool afterKlee=false,
                     int truthTableSeqCnt=-1,
                     bool origKlee=false) :
            trueCases(trueCases), falseCases(falseCases), conditions(conditions), decision(decision),
            testCaseFileNameList(testCaseFileNameList), afterKlee(afterKlee), truthTableSeqCnt(truthTableSeqCnt), origKlee(origKlee) {

        addAll(allCases, trueCases);
        addAll(allCases, falseCases);
        conditionNum = conditions.size();

        llvm::errs() << "------->>>   " << replaceEnterInStr(decision) << "   <<<-------\n";
        if (afterKlee)
            messageStr += "------->>>   "+replaceEnterInStr(decision)+"   <<<-------\n";

        if (MCCOutput) {
            if (allCases.size() != 0) {
                llvm::errs() << "\nMCC result is :\n";
                if (afterKlee) messageStr += "\nMCC result is :\n";
                printCases();
            }
            else {
                llvm::errs() << "Generate 0 MCC test case!\n";
                if (afterKlee) messageStr += "\nGenerate 0 MCC test case!\n";
            }

            if (afterKlee) {
                llvm::errs() << "MCC coverage : " << formatDoubleValue((double)allCases.size()*100/truthTableSeqCnt, 2) << "%\n\n";
                messageStr += "MCC : "+formatDoubleValue((double)allCases.size()*100/truthTableSeqCnt, 2)+"%\n\n";
                MCCGen += allCases.size();
                MCCAll += truthTableSeqCnt;
            }
            if (origKlee) {
                KMCCGen += allCases.size();
                KMCCAll += truthTableSeqCnt;
            }
        }

        if (MCCOutput) MCCTestCases = allCases;
        if (decisionCoverageOutput && (afterKlee || OrigKleeCov)) decisionTestCases = calculateDecision();
        if (conditionCoverageOutput && (afterKlee || OrigKleeCov)) conditionTestCases = calculateCondition();
        if (CDCOutput && (afterKlee || OrigKleeCov)) CDCTestCases = calculateCDC();
        if (MCDCOutput && (afterKlee || OrigKleeCov)) MCDCTestCases = calculateMCDC();

        llvm::errs() << "\n";
        if (afterKlee)
            messageStr += "\n";
        if (afterKlee && OrigKleeCov) {
            vector<pair<long long, long long> > t2;
            if (!trueCases.empty()) t2.push_back(trueCases.at(0));
            vector<pair<long long, long long> > f2;
            if (!falseCases.empty()) f2.push_back(falseCases.at(0));
            TestCaseSelector orig(t2, f2, conditions, decision, testCaseFileNameList,
                                              false, truthTableSeqCnt, true);
        }
    }
};


// 逻辑表达式树的节点类
// 要么同时存在左右孩子节点，表示操作符节点
// 要么是叶子节点，表示一个condition
class LogicExpressionNode {
public:
    shared_ptr<LogicExpressionNode> left, right, parent;
    vector<pair<long long, long long> > MCCTrueCase, MCCFalseCase;
    int conditionNum;
    int op;
    bool boolFlag;

    // 创建节点
    LogicExpressionNode() : op(0), boolFlag(false) {

    };

    // 节点要做非运算，交换T/F
    void swapMCCPostCase() {
        vector<pair<long long, long long> > tmp(std::move(MCCTrueCase));
        MCCTrueCase = std::move(MCCFalseCase);
        MCCFalseCase = std::move(tmp);
    }
};


// 逻辑操作符树
class LogicExpressionTree {
private:
    shared_ptr<LogicExpressionNode> root;
    string graphvizString;
    map<pair<long long, long long>, unsigned int> expect2SeqNum;

    // 判断该DeclRef指向的变量是否为bool类型
    bool isBoolTypeDeclRef(Expr *expr) {
        if (ImplicitCastExpr *implicitCastExpr = dyn_cast<ImplicitCastExpr>(expr))
            return isBoolTypeDeclRef(implicitCastExpr->getSubExpr());
        if (DeclRefExpr *declRefExpr = dyn_cast<DeclRefExpr>(expr)) {
            QualType type = declRefExpr->getDecl()->getType();
            LangOptions lo;
            PrintingPolicy pp(lo);
            string s;
            llvm::raw_string_ostream rso(s);
            type.print(rso, lo, llvm::Twine());
            string typeString = rso.str();
            if (typeString.compare("bool")==0 || typeString.compare("_Bool")==0) return true;
        }
        return false;
    }

    // 判断该表达式的结果是否为布尔量
    bool isBoolValue(Expr *expr) {
        if (ParenExpr *parenExpr = dyn_cast<ParenExpr>(expr))
            return isBoolValue(parenExpr->getSubExpr());
        if (CastExpr *castExpr = dyn_cast<CastExpr>(expr))
            return isBoolValue(castExpr->getSubExpr());
        if (isBoolTypeDeclRef(expr)) return true;
        if (BinaryOperator *binaryOperator = dyn_cast<BinaryOperator>(expr))
            if (binaryOperator->isLogicalOp() || binaryOperator->isComparisonOp())
                return true;
        if (UnaryOperator *unaryOperator = dyn_cast<UnaryOperator>(expr))
            if (unaryOperator->getOpcode() == UO_LNot)
                return true;
        return false;
    }

    // 判断该表达式是否为condition
    bool isCondition(Expr *expr) {
        // expr is a binaryOperator
        if (isBoolTypeDeclRef(expr)) return true;
        if (BinaryOperator *binaryOperator = dyn_cast<BinaryOperator>(expr)) {
            if (binaryOperator->isLogicalOp()) return false;
            if (binaryOperator->isRelationalOp()) return true;
            if (binaryOperator->isEqualityOp()) {
                Expr *lhs = binaryOperator->getLHS();
                Expr *rhs = binaryOperator->getRHS();
                // 若等号/不等号两边都是布尔量，则该等号表示逻辑异或/同或，等号两边可以继续分
                if (!isBoolValue(lhs) || !isBoolValue(rhs)) return true;
            }
        }
        return false;
    }

    // 递归遍历decision表达式，提取condition并创建node
    bool travelExpr(Expr *expr, shared_ptr<LogicExpressionNode> node) {
        // ! node 非运算
        if (UnaryOperator *unaryOperator = dyn_cast<UnaryOperator>(expr)) {
            if (unaryOperator->getOpcode() == UO_LNot) {
                node->op ^= NOT;
                if (DEBUG) llvm::errs() << "Not expr : " << sourceCode.getRewrittenText(expr->getSourceRange()) << "\n";
                return travelExpr(unaryOperator->getSubExpr(), node);
            }
            else {
                llvm::errs() << "Error UnaryOperator : " << sourceCode.getRewrittenText(expr->getSourceRange()) << "\n";
                node->conditionNum = conditions.size();
                conditions.push_back(expr);
                return false;
            }
        }
            // ParenExpr 括号
        else if (ParenExpr *parenExpr = dyn_cast<ParenExpr>(expr)) {
            if (DEBUG) llvm::errs() << "ParenExpr : " << sourceCode.getRewrittenText(expr->getSourceRange()) << "\n";
            return travelExpr(parenExpr->getSubExpr(), node);
        }
            // CastExpr 类型转换
        else if (CastExpr *castExpr = dyn_cast<CastExpr>(expr)) {
            if (DEBUG) llvm::errs() << "CastExpr : " << sourceCode.getRewrittenText(expr->getSourceRange()) << "\n";
            return travelExpr(castExpr->getSubExpr(), node);
        }
            // condition
        else if (isCondition(expr)) {
            if (DEBUG) llvm::errs() << "Condition : " << sourceCode.getRewrittenText(expr->getSourceRange()) << "\n";
            node->conditionNum = conditions.size();
            conditions.push_back(expr);
            return true;
        }
            // dividable 二元运算符
        else if (BinaryOperator *binaryOperator = dyn_cast<BinaryOperator>(expr)) {
            if (DEBUG) llvm::errs() << "BinaryOperator : " << sourceCode.getRewrittenText(expr->getSourceRange()) <<
                                    "\nLHS : " << sourceCode.getRewrittenText(binaryOperator->getLHS()->getSourceRange()) << "    RHS : " <<
                                    sourceCode.getRewrittenText(binaryOperator->getRHS()->getSourceRange()) << "\n";
            switch (binaryOperator->getOpcode()) {
                case BO_LAnd: node->op ^= AND; break;
                case BO_LOr: node->op ^= OR; break;
                case BO_EQ: node->op ^= XOR; node->op ^= NOT; break;
                case BO_NE: node->op ^= XOR; break;
                default :
                    if (DEBUG) llvm::errs() << "Condition : " << sourceCode.getRewrittenText(expr->getSourceRange()) << "\n";
                    node->conditionNum = conditions.size();
                    conditions.push_back(expr);
                    return true;
            }
            node->left = make_shared<LogicExpressionNode>();
            node->left->parent = node;
            node->right = make_shared<LogicExpressionNode>();
            node->right->parent = node;
            bool lhs = travelExpr(binaryOperator->getLHS(), node->left);
            bool rhs = travelExpr(binaryOperator->getRHS(), node->right);
            return lhs && rhs;
        }
            // 单独的值 e.g. if(tmp)
        else if (isa<DeclRefExpr>(expr)) {
            if (DEBUG) llvm::errs() << "Condition : " << sourceCode.getRewrittenText(expr->getSourceRange()) << "\n";
            node->conditionNum = conditions.size();
            conditions.push_back(expr);
            return true;
        }
            // 函数调用 e.g. if(func(tmp))
        else if (isa<CallExpr>(expr)) {
            if (DEBUG) llvm::errs() << "Function Call : " << sourceCode.getRewrittenText(expr->getSourceRange()) << "\n";
            node->conditionNum = conditions.size();
            conditions.push_back(expr);
            return true;
        }
        else {
            llvm::errs() << "ERROR not matched : " << sourceCode.getRewrittenText(expr->getSourceRange()) << "\n";
            node->conditionNum = conditions.size();
            conditions.push_back(expr);
            return false;
        }
    }

    string getOpString(int op) {
        switch (op) {
            case 1: return "OR";
            case 2: return "AND";
            case 4: return "XOR";
            case 9: return "! OR";
            case 10: return "! AND";
            case 12: return "! XOR";
            default: return "ERROR";
        }
    }

    // 遍历以输出树的结构 graphviz格式
    void travelTree(shared_ptr<LogicExpressionNode> node, int count) {
        if (node->op == 0) {
            graphvizString += "condition" + to_string(node->conditionNum) + " [label=\"" +
                              sourceCode.getRewrittenText(conditions.at(node->conditionNum)->getSourceRange()) + "\"]\n";
            return;
        }
        if (node->op == 8) {
            graphvizString += "condition" + to_string(node->conditionNum) + " [label=\"!(" +
                              sourceCode.getRewrittenText(conditions.at(node->conditionNum)->getSourceRange()) + ")\"]\n";
            return;
        }
        graphvizString += "op" + to_string(count) + " [label=\"" + getOpString(node->op) + "\"]\n";

        if (node->left->op == 0 || node->left->op == 8)
            graphvizString += "op" + to_string(count) + " -> condition" + to_string(node->left->conditionNum) + "\n";
        else
            graphvizString += "op" + to_string(count) + " -> op" + to_string(count*2) + "\n";

        if (node->right->op == 0 || node->right->op == 8)
            graphvizString += "op" + to_string(count) + " -> condition" + to_string(node->right->conditionNum) + "\n";
        else
            graphvizString += "op" + to_string(count) + " -> op" + to_string(count*2+1) + "\n";

        travelTree(node->left, count*2);
        travelTree(node->right, count*2+1);
    }

    pair<long long, long long> mergeCaseState(pair<long long, long long> p1, pair<long long, long long> p2) {
        return make_pair(p1.first | p2.first, p1.second | p2.second);
    }

    // 后序遍历生成MCC测试用例（即真值表）
    void MCCPostOrderTraversal(shared_ptr<LogicExpressionNode> node) {
        node->MCCTrueCase.clear();
        node->MCCFalseCase.clear();
        // 该节点是二元逻辑运算符节点
        if (NULL != node->left) {
            // 后序遍历
            MCCPostOrderTraversal(node->left);
            MCCPostOrderTraversal(node->right);
            // 该节点需要做与运算
            if ((node->op & AND) != 0) {
                for (pair<long long, long long> leftTrue : node->left->MCCTrueCase) {
                    // TTT
                    for (pair<long long, long long> rightTrue : node->right->MCCTrueCase) {
                        node->MCCTrueCase.push_back(mergeCaseState(leftTrue, rightTrue));
                    }
                    // TFF
                    for (pair<long long, long long> rightFalse : node->right->MCCFalseCase) {
                        node->MCCFalseCase.push_back(mergeCaseState(leftTrue, rightFalse));
                    }
                }
                // FXF
                addAll(node->MCCFalseCase, node->left->MCCFalseCase);
            }
                // 该节点需要做或运算
            else if ((node->op & OR) != 0) {
                // TXT
                addAll(node->MCCTrueCase, node->left->MCCTrueCase);
                for (pair<long long, long long> leftFalse : node->left->MCCFalseCase) {
                    // FTT
                    for (pair<long long, long long> rightTrue : node->right->MCCTrueCase) {
                        node->MCCTrueCase.push_back(mergeCaseState(leftFalse, rightTrue));
                    }
                    // FFF
                    for (pair<long long, long long> rightFalse : node->right->MCCFalseCase) {
                        node->MCCFalseCase.push_back(mergeCaseState(leftFalse, rightFalse));
                    }
                }
            }
                // 该节点需要做异或运算
            else {
                for (pair<long long, long long> leftFalse : node->left->MCCFalseCase) {
                    // FTT
                    for (pair<long long, long long> rightTrue : node->right->MCCTrueCase) {
                        node->MCCTrueCase.push_back(mergeCaseState(leftFalse, rightTrue));
                    }
                    // FFF
                    for (pair<long long, long long> rightFalse : node->right->MCCFalseCase) {
                        node->MCCFalseCase.push_back(mergeCaseState(leftFalse, rightFalse));
                    }
                }
                for (pair<long long, long long> leftTrue : node->left->MCCTrueCase) {
                    // TTF
                    for (pair<long long, long long> rightTrue : node->right->MCCTrueCase) {
                        node->MCCFalseCase.push_back(mergeCaseState(leftTrue, rightTrue));
                    }
                    // TFT
                    for (pair<long long, long long> rightFalse : node->right->MCCFalseCase) {
                        node->MCCTrueCase.push_back(mergeCaseState(leftTrue, rightFalse));
                    }
                }
            }
        }
            // 是叶子节点，表示原子condition
        else {
            node->MCCTrueCase.push_back(make_pair(1LL<<(node->conditionNum), 1LL<<(node->conditionNum)));
            node->MCCFalseCase.push_back(make_pair(0LL<<(node->conditionNum), 1LL<<(node->conditionNum)));
        }

        // 该节点需要做非运算
        if ((node->op & NOT) != 0) {
            node->swapMCCPostCase();
        }
    }

public:
    vector<LogicExpressionNode> conditionNodes;
    Expr* decision;
    vector<Expr*> conditions;
    vector<pair<long long, long long> > MCCExpect;
    vector<pair<long long, long long> > MCCExpectTrue;
    vector<pair<long long, long long> > MCCExpectFalse;

    shared_ptr<LogicExpressionNode> getRoot() { return root; }

    // 输出树的结构 graphviz格式
    string printTree() {
        graphvizString = "digraph G {\nnode [shape=circle width=1 style=filled]\nedge [arrowhead=vee]\nlabelloc=\"t\"\nlabel=\"";
        graphvizString += sourceCode.getRewrittenText(decision->getSourceRange())+"\"\n";
        if (root->op == 0)
            if (conditions.size() > 0)
                graphvizString += sourceCode.getRewrittenText(conditions.at(0)->getSourceRange())+"\n";
            else
                graphvizString += "ERROR";
        else
            travelTree(root, 1);
        graphvizString += "}\n";
        llvm::errs() << graphvizString;

        return graphvizString;
    }

    // 计算MCC
    void calculateMCC() {
        MCCPostOrderTraversal(root);
        addAll(MCCExpect, root->MCCTrueCase);
        addAll(MCCExpect, root->MCCFalseCase);
        addAll(MCCExpectTrue, root->MCCTrueCase);
        addAll(MCCExpectFalse, root->MCCFalseCase);
    }

    // 将相关信息添加到全局变量中
    void makeExpect2SeqNumMap() {
        if (MCCExpect.empty()) calculateMCC();
        expect2SeqNum.clear();
        map<unsigned int, pair<long long, long long> > trueSeqNum2Expect;
        map<unsigned int, pair<long long, long long> > falseSeqNum2Expect;
        for (unsigned int i=0; i< MCCExpect.size(); i++)
            expect2SeqNum.insert(make_pair(MCCExpect.at(i), i));
        for (unsigned int i=0; i<root->MCCTrueCase.size(); i++)
            trueSeqNum2Expect.insert(make_pair(i, root->MCCTrueCase.at(i)));
        for (unsigned int i=0; i<root->MCCFalseCase.size(); i++)
            falseSeqNum2Expect.insert(make_pair(i+root->MCCTrueCase.size(), root->MCCFalseCase.at(i)));

        expect2SeqNumList.push_back(expect2SeqNum);
        trueSeqNum2ExpectList.push_back(std::move(trueSeqNum2Expect));
        falseSeqNum2ExpectList.push_back(std::move(falseSeqNum2Expect));
    }

    map<pair<long long, long long>, unsigned int> getSeqNumMap() {
        map<pair<long long, long long>, unsigned int> result;
        for (pair<pair<long long, long long>, unsigned int> item : expect2SeqNum)
            result.insert(item);
        return result;
    }

    // 遍历decision表达式创建逻辑表达式树
    explicit LogicExpressionTree(Expr *decision) : decision(decision) {
        root = make_shared<LogicExpressionNode>();
        bool ifError = travelExpr(decision, root);
        if (!ifError) llvm::errs() << "ERROR illegal decision : " << sourceCode.getRewrittenText(decision->getSourceRange()) << "\n";

        if (DEBUG) {
            llvm::errs() << "\n";
            printTree();
        }

        calculateMCC();
        makeExpect2SeqNumMap();

        vector<string> conditionText;
        for (Expr * expr : conditions) {
            conditionText.push_back(sourceCode.getRewrittenText(expr->getSourceRange()));
        }
        string decisionText = sourceCode.getRewrittenText(decision->getSourceRange());
        TestCaseSelector testCaseSelector(root->MCCTrueCase, root->MCCFalseCase, conditionText, decisionText);
        conditionTextList.push_back(std::move(conditionText));
        decisionTextList.push_back(replaceEnterInStr(decisionText));
    }
};

string kleeInclude = "#include <klee/klee.h>\n";

// 每一位表示一个condition
// expect表示期望的输出 为0表示该位为false 为1表示该位为true
// SCMask表示哪些位是被短路的 为1表示该位没有被短路 为0表示该位被短路
string tmpVarDeclStmt = "\nint __Cond_Value__;\n";
const char kappaDeclFmt[128] = "long long __kappa__%d__;\n";
const char expectDeclFmt[128] = "#define __expect__%d__%d__%u__ %lld\n";
const char SCMaskDeclFmt[128] = "#define __SCMask__%d__%d__%u__ %lld\n";
const char kappaRstFmt[128] = "(__kappa__%d__ = 0),\n";
const char kappaCalcFmt[128] = "((__kappa__%d__ |= (1LL*((%s)!=0)<<%d)), (__kappa__%d__ & 1LL<<%d)!=0)\n";
const char decisionReplaceFmt[128] = "(%s(__Cond_Value__ = %s),\n%s__Cond_Value__)";

const char kappaMatchFmt[128] = "%s(__kappa__%d__ != __expect__%d__%d__%u__),\n";
const char switchMatchFmt[128] = "%s(%d*0);\n";

string openMergeStmt = "\nklee_open_merge();\n";
string closeMergeStmt = "\nklee_close_merge();\n";

const char expectPathStmt[128] = "#define __expect__%d__%d %d\n";
const char expectSwitchPathStmt[128] = "#define __expect_s__%d__%d %d\n";
const char pathStmt[128] = "int __path__%d = -1;\n";
const char switchPathStmt[128] = "int __path_s__%d = -1;\n";
const char pathRecordStmt[128] = "__path__%d = __Cond_Value__,\n";
const char switchPathRecordStmt[128] = "__path_s__%d = %d;\n";
const char wholePathMatchStmt[128] = "%s(!(%s));\n";
const char pathMatchStmt[128] = "(__path__%d == __expect__%d__%d)";
const char switchPathMatchStmt[128] = "(__path_s__%d == __expect_s__%d__%d)";

#define MODE_ALL 3
#define MODE_DEC 2
#define MODE_SEQ 1
#define MODE_NONE -1

// 操作Rewriter类，用于方便地对Rewriter类做添加kappa stmt、将内容写入本地、重置Rewriter内容等操作
class RewriterController {
private:
    ASTContext *astContext;
    shared_ptr<CustomRewriter> rewriter;
    int count;
    int mode;
    string coverage;
    vector<pair<SourceLocation, string>> decisionTextList;
    vector<pair<SourceLocation, string>> mergeTextList;
    set<SourceLocation> funcLocSet;

    // 将编辑后的内容写入本地
    void writeNewFile(shared_ptr<CustomRewriter> rewriter, string pathString, string coverage, int mode=-1, int count=0) {
        fs::path rawPath(pathString);
        fs::path fileDir = rawPath.parent_path();
        fileDir /= resultDirStr;

        if (coverage == "statement")
            fileDir /= "Statement";
        else if (coverage == "path")
            fileDir /= "Path";
        else
            fileDir /= KappaSubDirNameStr;

        string fileName = rawPath.filename().string();
        if (mode == MODE_DEC || mode == MODE_SEQ) fileName.insert(fileName.rfind('.'), "_"+to_string(count));

        if (coverage == "statement" || coverage == "path")
            fileDir /= fileName;
        else
            fileDir /= "kappa-"+fileName;
        string filePath = fileDir.string();

#if CLANG_VERSION == 3
        string ErrorInfo;
        llvm::raw_fd_ostream outFile(filePath.c_str(), ErrorInfo, llvm::sys::fs::F_None);
#else
        std::error_code ErrorInfo;
        llvm::raw_fd_ostream outFile(filePath.c_str(), ErrorInfo);
#endif
        getEditBuffer(sourceCode.getSourceMgr().getMainFileID()).write(outFile); // --> this will write the result to outFile
        outFile.close();
    }

    // 后处理，添加include、桩函数，删除extern关键词
    void postEditRewriter() {
        SourceManager &SM = rewriter->getSourceMgr();
        SourceLocation fileStartLoc = SM.getLocForStartOfFile(SM.getMainFileID());

        // 添加include文本
        if (addInclude) {
            InsertTextAfter(fileStartLoc, kleeInclude);
        }

        // 添加path断言
        if (EnableSpecPath) {
            string pathMatchString;
            char buffer[MAX_BUFFER_SIZE];
#ifndef TRIGGER
            char assertFuncName[64] = "klee_assert";
#else
            char assertFuncName[64] = "klee_trigger_if_false";
#endif

            for (int j=0; j<pathCount; j++) {
                pathMatchString = "";
                for (int i=0; i<specifiedPathCount; i++) {
                    if (specifiedPath.at(j).at(i) == -2) continue;
                    sprintf(buffer, pathMatchStmt, i, j, i);
                    if (pathMatchString != "") pathMatchString += " && ";
                    pathMatchString += buffer;
                }
                for (int i=0; i<switchPathCount; i++) {
                    if (switchPath.at(j).at(i) == -2) continue;
                    sprintf(buffer, switchPathMatchStmt, i, j, i);
                    if (pathMatchString != "") pathMatchString += " && ";
                    pathMatchString += buffer;
                }
                sprintf(buffer, wholePathMatchStmt, assertFuncName, pathMatchString.c_str());

                makeSymbolicStmt += "    ";
                makeSymbolicStmt += buffer;
            }
        }

        // 添加驱动函数文本
        if (addDriverFunc) {
            if (targetFuncName.compare("main")==0) {
                Stmt *mainBody = mainFuncDecl->getBody();
                if (CompoundStmt *compoundStmt = dyn_cast<CompoundStmt>(mainBody)) {
                    if (!compoundStmt->body_empty()) {
                        Stmt *firstStmt = *(compoundStmt->body_begin());
                        InsertTextAfter(firstStmt->getSourceRange().getBegin(), makeSymbolicStmt);
                    }
                }
            }
            else {
                if (hasMain) {
                    ReplaceText(mainFuncDecl->getBody()->getSourceRange(), " {\n"+makeSymbolicStmt+"    return 0;\n}\n");
                }
                else {
                    InsertTextAfter(SM.getLocForEndOfFile(SM.getMainFileID()), "int main() {\n"+makeSymbolicStmt+"}\n");
                }
            }
        }

        // 添加tmp变量定义
        InsertTextAfter(fileStartLoc, tmpVarDeclStmt);

        // 删除extern关键词
        for (VarDecl* externVarDel : externVariables) {
            string varDeclStr = getRewrittenText(externVarDel->getSourceRange());
            string::size_type pos = varDeclStr.find("extern ");
            if (pos != string::npos) {
                varDeclStr.replace(pos, 7, "");
                ReplaceText(externVarDel->getSourceRange(), varDeclStr);
            }
        }

        // 添加原decision注释
        for (pair<SourceLocation, string> decisionText : decisionTextList)
            InsertTextAfter(decisionText.first, decisionText.second);

        // 添加klee_merge
#if CLANG_VERSION > 3
        if (EnableMerge) {
            for (pair<SourceLocation, string> mergeText : mergeTextList) {
//                if ((mergeText == mergeTextList.at(mergeTextList.size()-1))) continue;
                InsertTextAfter(mergeText.first, mergeText.second);
            }
        }
#endif

        // 添加path定义
        if (EnableSpecPath) {
            char buffer[MAX_BUFFER_SIZE];
            for (int j=0; j<pathCount; j++) {
                for (int i=0; i<specifiedPathCount; i++) {
                    if (i > specifiedPath.at(j).size()) llvm::errs() << "SpecPath Str ERROR!";
                    sprintf(buffer, expectPathStmt, j, i, specifiedPath.at(j).at(i));
                    InsertTextAfter(fileStartLoc, buffer);
                }
                for (int i=0; i<switchPathCount; i++) {
                    if (i > switchPath.at(j).size()) llvm::errs() << "SpecPath Str ERROR!";
                    sprintf(buffer, expectSwitchPathStmt, j, i, switchPath.at(j).at(i));
                    InsertTextAfter(fileStartLoc, buffer);
                }
            }
            for (int i=0; i<specifiedPathCount; i++) {
                sprintf(buffer, pathStmt, i);
                InsertTextAfter(fileStartLoc, buffer);
            }
            for (int i=0; i<switchPathCount; i++) {
                sprintf(buffer, switchPathStmt, i);
                InsertTextAfter(fileStartLoc, buffer);
            }
        }
    }

    // 重置Rewriter，恢复原始文本
    void resetRewriter() {
        rewriter = make_shared<CustomRewriter>();
        rewriter->setSourceMgr(astContext->getSourceManager(), astContext->getLangOpts());
        decisionTextList.clear();
        mergeTextList.clear();
        funcLocSet.clear();
        triggerNum = 0;
    }

    // 自动添加行首空格
    string addIndentation(string str, SourceLocation loc, int offset=0) {
        string indentation = "";
        // 获取该位置之前的文本
        SourceManager &SM = rewriter->getSourceMgr();
        SourceLocation fileStartLoc = SM.getLocForStartOfFile(SM.getMainFileID());
        SourceRange range(fileStartLoc, loc);
        string textBefore = sourceCode.getRewrittenText(range);
        // 找到之前文本的最后一个换行符
        string::size_type from = textBefore.rfind("\n");
        // 获取该换行符后的连续空白字符
        if (from != string::npos) {
            from++;
            string::size_type pos;
            for (pos = from; pos<textBefore.size(); pos++)
                if (textBefore.at(pos)!=' ' && textBefore.at(pos)!='\t') break;
            indentation = textBefore.substr(from, pos-from);
        }
        for (int i=0; i<offset; i++)
            indentation += " ";
        if (indentation == "") return str;

        // 为待处理字符串的每个换行符后面添加空白字符，若换行符后已经有空白字符，则不添加
        string::size_type enterLoc = str.size();
        while (enterLoc != string::npos && enterLoc != 0) {
            enterLoc = str.rfind("\n", enterLoc-1);
            if (enterLoc != string::npos &&
                (enterLoc==str.size()-1 || (str.at(enterLoc+1)!=' ' && str.at(enterLoc+1)!='\t'))) {
                str.insert(enterLoc+1, indentation);
            }
        }
        return str;
    }


public:
    RewriterController(ASTContext *astContext, int mode=MODE_NONE, string coverage="") : count(0) {
        this->mode = mode;
        this->coverage = coverage;
        this->astContext = astContext;
        resetRewriter();
    }

    shared_ptr<CustomRewriter> getRewriter() { return rewriter; }

    // 添加decision注释
    void addDecisionText(SourceLocation loc, string text) {
        decisionTextList.push_back(make_pair(loc, "\n// "+replaceEnterInStr(text)+"\n"));
    }

    // 将编辑后的内容写入本地
    void writeResult() {
        postEditRewriter();

        writeNewFile(rewriter, pathString, coverage, mode, count);
        count++;
        triggerNumSet.push_back(triggerNum);

        resetRewriter();
    }

    // 添加kappa stmt
    void editRewriter(Expr *decision, vector<Expr*> &conditions, vector<pair<long long, long long> > &expect,
                      map<pair<long long, long long>, unsigned int> &expect2SeqNum,
                      SourceLocation declLoc, SourceLocation decisionStartLoc, SourceLocation stmtEndLoc, SourceRange decisionSourceRange,
                      int decisionCount, unsigned int trueCaseNum, bool isLoop=false) {
        char buffer[MAX_BUFFER_SIZE];

        // 替换condition
        for (unsigned int i=0; i<conditions.size(); i++) {
            string conditionString = sourceCode.getRewrittenText(conditions.at(i)->getSourceRange());
            sprintf(buffer, kappaCalcFmt, decisionCount, conditionString.c_str(), i, decisionCount, i);
            ReplaceText(conditions.at(i)->getSourceRange(), buffer, decisionStartLoc, INDENTATION_NUM+8);
        }

#ifndef TRIGGER
        char assertFuncName[64] = "klee_assert";
#else
        char triggerFuncName[64] = "klee_trigger_if_false";
        char triggerAndTerminateFuncName[64] = "klee_trigger_and_terminate_if_false";
        char * assertFuncName = (KappaMode==KappaGeneratePolicy::All || (!EarlyStop && KappaMode==KappaGeneratePolicy::Decision))?triggerFuncName:triggerAndTerminateFuncName;
#endif

        // 生成断言语句
        string kappaMatchStmt = "";
        if (KleePrintMode) {
            string matchStmt = "printf(\"{\\\"Kappa"+to_string(decisionCount)+"\\\":%lld, \\\"size\\\":"
                    + to_string(expect.size()) +", \\\"result\\\":%d}\\n\", klee_get_valuell(__kappa__"+to_string(decisionCount)+"__), klee_get_value_i32(__Cond_Value__));";
            InsertTextAfter(stmtEndLoc, matchStmt);
        } else{
            for (unsigned int i=0; i<expect.size(); i++) {
#ifdef TRIGGER
                // 是循环且为Decision模式，需要特殊判断
                if (isLoop && KappaMode==KappaGeneratePolicy::Decision){
                    // 逻辑表达式值为真，循环没有结束，需要继续运行
                    if (i < trueCaseNum)
                        assertFuncName = triggerFuncName;
                        // 逻辑表达式值为假，循环结束，提前结束运行
                    else
                        assertFuncName = triggerAndTerminateFuncName;
                }
#endif

                sprintf(buffer, kappaMatchFmt, assertFuncName, decisionCount, decisionCount, i, expect2SeqNum[expect.at(i)]);
                kappaMatchStmt += buffer;
            }
        }

        if (EnableSpecPath) {
            kappaMatchStmt = "";
            sprintf(buffer, pathRecordStmt, specifiedPathCount);
            kappaMatchStmt += buffer;
            specifiedPathCount++;
        }

        // 替换整个decision
        char kappaRstStmt[MAX_BUFFER_SIZE];
        sprintf(kappaRstStmt, kappaRstFmt, decisionCount);
        sprintf(buffer, decisionReplaceFmt, kappaRstStmt, getRewrittenText(decisionSourceRange).c_str(),
                kappaMatchStmt.c_str());
        ReplaceText(decisionSourceRange, buffer, decisionStartLoc, INDENTATION_NUM);

        // 添加原decision注释
        string text = sourceCode.getRewrittenText(decision->getSourceRange());
        InsertTextAfter(declLoc, "\n// "+replaceEnterInStr(text)+"\n");

        // 添加kappa定义
        sprintf(buffer, kappaDeclFmt, decisionCount);
        InsertTextAfter(declLoc, buffer);

        // 添加expect和SCMask定义
        for (unsigned int i=0; i<expect.size(); i++) {
            // 添加每条真值表注释
            string valueComment = "// ";
            for (unsigned int j=0; j<conditions.size(); j++) {
                if (!(expect.at(i).second & 1<<j))
                    valueComment += "X";
                else if (expect.at(i).first & 1<<j)
                    valueComment += "T";
                else
                    valueComment += "F";
            }
            valueComment += "|";
            valueComment += i<trueCaseNum?"T":"F";
            valueComment += "\n";
            InsertTextAfter(declLoc, valueComment);

            sprintf(buffer, expectDeclFmt, decisionCount, i, expect2SeqNum[expect.at(i)], expect.at(i).first & expect.at(i).second);
            InsertTextAfter(declLoc, buffer);

            sprintf(buffer, SCMaskDeclFmt, decisionCount, i, expect2SeqNum[expect.at(i)], expect.at(i).second);
            InsertTextAfter(declLoc, buffer);
        }

        // 添加原decision注释
        addDecisionText(decisionStartLoc, sourceCode.getRewrittenText(decision->getSourceRange()));

        // 添加klee_merge
        if (funcLocSet.count(declLoc) == 0) {
            funcLocSet.insert(declLoc);
            mergeTextList.push_back(make_pair(decisionStartLoc, openMergeStmt));
        }
        else {
            mergeTextList.push_back(make_pair(decisionStartLoc, closeMergeStmt));
            mergeTextList.push_back(make_pair(decisionStartLoc, openMergeStmt));
        }
    }

    // 添加kappa stmt 单个expect
    void editRewriter(Expr *decision, vector<Expr*> &conditions, pair<long long, long long> &expect,
                      map<pair<long long, long long>, unsigned int> &expect2SeqNum,
                      SourceLocation declLoc, SourceLocation decisionStartLoc, SourceLocation stmtEndLoc, SourceRange decisionSourceRange, int decisionCount, unsigned int trueCaseNum) {
        vector<pair<long long, long long> > expectVector;
        expectVector.push_back(expect);
        editRewriter(decision, conditions, expectVector, expect2SeqNum, declLoc, decisionStartLoc, stmtEndLoc, decisionSourceRange, decisionCount, trueCaseNum);
    }

    void InsertTextBefore(SourceLocation loc, string str, int offset=0) {
        rewriter->InsertTextBefore(loc, addIndentation(str, loc, offset));
    }

    void InsertTextAfter(SourceLocation loc, string str, int offset=0) {
        rewriter->InsertTextAfter(loc, addIndentation(str, loc, offset));
    }

    void ReplaceText(SourceRange range, string str) {
        rewriter->ReplaceText(range, str);
    }

    void ReplaceText(SourceRange range, string str, SourceLocation loc, int offset=0) {
        rewriter->ReplaceText(range, addIndentation(str, loc, offset));
    }

    string getRewrittenText(SourceRange range) const { return rewriter->getRewrittenText(range); }

    RewriteBuffer &getEditBuffer(FileID FID) { return rewriter->getEditBuffer(FID); }

    SourceManager &getSourceMgr() const { return rewriter->getSourceMgr(); }
};


shared_ptr<RewriterController> rewriterController;


// 消去字符串中的特定字符
string eraseChar(string &str, char ch) {
    string::size_type pos = str.find_first_of(ch);
    while (pos != string::npos) {
        str.erase(pos, 1);
        pos = str.find_first_of(ch);
    }
    return str;
}

char makeSymbolicFmt[128] = "klee_make_symbolic(%s, sizeof(%s), \"%s\");\n";
char arrayAssumeFmt[128] = "for (int __arrIdx__ = 0; __arrIdx__ < sizeof(%s)/sizeof(%s[0]); __arrIdx__++)\n";
char upperBoundAssumeFmt[128] = "klee_assume(%s < %d);\n";
char lowerBoundAssumeFmt[128] = "klee_assume(%s > -%d);\n";

// visitor 生成驱动函数
class DriverFuncGenerateVisitor : public RecursiveASTVisitor<DriverFuncGenerateVisitor> {
private:
    ASTContext *astContext;

    // 获得array变量的元素类型
    const clang::Type * getRawElementTypeOfArray(const clang::Type *arrayType) {
        const clang::Type *arrayElementType = arrayType->getArrayElementTypeNoTypeQual();
        return arrayElementType->isArrayType()?getRawElementTypeOfArray(arrayElementType):arrayElementType;
    }

    // 添加变量定义
    bool insertSymbolicVar(QualType rawType, VarDecl *varDecl, bool isParam) {
        QualType qualType = rawType.getNonReferenceType().getUnqualifiedType();
        string varType = qualType.getAsString(printingPolicy);
        string varName = varDecl->getNameAsString();
        const clang::Type *type = qualType.getTypePtr()->getUnqualifiedDesugaredType();
        string varDeclText = varType + " " + varName;
        string paramDeclText = sourceCode.getRewrittenText(varDecl->getSourceRange());
        eraseChar(paramDeclText, '&');
        if (DEBUG) {
            if (varDecl->hasExternalStorage())
                llvm::errs() << "Found extern var : [" << varType << "] " << varName << "!\n";
            else
                llvm::errs() << "Found var : [" << varType << "] " << varName << "!\n";
        }

        char buffer[MAX_BUFFER_SIZE];

        if (vars.count(varName) == 1) return false;
        if (type->isFunctionType()) {
            llvm::errs() << "ERROR : [" << varType << "] " << varName << " is a function!\n";
            return false;
        }
        if (type->isIncompleteArrayType()) {
            llvm::errs() << "ERROR : [" << varType << "] " << varName << " is a IncompleteArrayType!\n";
            return false;
        }
        if (type->isVariableArrayType()) {
            llvm::errs() << "ERROR : [" << varType << "] " << varName << " is a VariableArrayType!\n";
            return false;
        }
        if (type->isDependentSizedArrayType()) {
            llvm::errs() << "ERROR : [" << varType << "] " << varName << " is a DependentSizedArrayType!\n";
            return false;
        }
        // 只支持一级指针
        if (type->isPointerType()) {
            QualType pointeeType = type->getPointeeType().getUnqualifiedType();
            if (pointeeType->isPointerType()) {
                llvm::errs() << "ERROR : [" << varType << "] " << varName << " is a PointerType pointing to another point!\n";
                return false;
            }
            if (type->isFunctionPointerType()) {
                llvm::errs() << "ERROR : [" << varType << "] " << varName << " is a PointerType pointing to function!\n";
                return false;
            }
            if (NULL != type->getPointeeCXXRecordDecl()) {
                llvm::errs() << "WARNING : [" << varType << "] " << varName << " is a PointerType pointing to c++ struct/union/class!\n";
            }
                // 先定义指针指向的变量，再将指针变量赋值
            else {
                if (!pointeeType.getTypePtr()->getUnqualifiedDesugaredType()->isFundamentalType()) {
                    llvm::errs() << "WARNING : [" << varType << "] " << varName << " is not a support type variable!\n";
                }
                string newVarDeclText = pointeeType.getAsString(printingPolicy) + " ___"+varName+"___";
                makeSymbolicStmt += "    "+newVarDeclText+";\n";
                if (isParam) {
                    makeSymbolicStmt += "    "+paramDeclText+" = &___"+varName+"___;\n";
                }
                else {
                    makeSymbolicStmt += "    "+varName+" = &___"+varName+"___;\n";
                }

                sprintf(buffer, makeSymbolicFmt, ("&___"+varName+"___").c_str(), ("___"+varName+"___").c_str(),
                        (varDeclText + " ---> " + newVarDeclText).c_str());
                makeSymbolicStmt += "    ";
                makeSymbolicStmt += buffer;

                if (boundary>0 && pointeeType.getTypePtr()->getUnqualifiedDesugaredType()->isIntegerType()) {
                    sprintf(buffer, upperBoundAssumeFmt, varName.c_str(), (int) boundary);
                    makeSymbolicStmt += "    ";
                    makeSymbolicStmt += buffer;
                    sprintf(buffer, lowerBoundAssumeFmt, varName.c_str(), (int) boundary);
                    makeSymbolicStmt += "    ";
                    makeSymbolicStmt += buffer;
                }

                return true;
            }
        }
        else if (type->isArrayType()) {
            const clang::Type *arrayElementType = getRawElementTypeOfArray(type);
            if (arrayElementType->isPointerType()) {
                llvm::errs() << "ERROR : [" << varType << "] " << varName << " is an array of pointer!\n";
                return false;
            }
            if (isParam) makeSymbolicStmt += "    "+paramDeclText+";\n";
            sprintf(buffer, makeSymbolicFmt, varName.c_str(), varName.c_str(), varDeclText.c_str());
            makeSymbolicStmt += "    ";
            makeSymbolicStmt += buffer;

            if (boundary>0 && arrayElementType->isIntegerType()) {
                sprintf(buffer, arrayAssumeFmt, varName.c_str(), varName.c_str());
                makeSymbolicStmt += "    ";
                makeSymbolicStmt += buffer;
                makeSymbolicStmt += "    {\n";
                sprintf(buffer, upperBoundAssumeFmt, (varName+"[__arrIdx__]").c_str(), (int) boundary);
                makeSymbolicStmt += "        ";
                makeSymbolicStmt += buffer;
                sprintf(buffer, lowerBoundAssumeFmt, (varName+"[__arrIdx__]").c_str(), (int) boundary);
                makeSymbolicStmt += "        ";
                makeSymbolicStmt += buffer;
                makeSymbolicStmt += "    }\n";
//                if (const ConstantArrayType *arr = dyn_cast<ConstantArrayType>(type)) {
//                    int arrLen = *(arr->getSize().getRawData());
//                }
            }

            return true;
        }
        else if (NULL != type->getAsCXXRecordDecl()) {
            llvm::errs() << "WARNING : [" << varType << "] " << varName << " is a c++ struct/union/class!\n";
        }
        else if (type->isStructureType()) {
            llvm::errs() << "WARNING : [" << varType << "] " << varName << " is a structural type and will be regarded as ONE number!\n";
        }
        else if (!type->isFundamentalType()) {
            llvm::errs() << "WARNING : [" << varType << "] " << varName << " is not a support type variable!\n";
        }
        if (isParam) makeSymbolicStmt += "    "+paramDeclText+";\n";
        sprintf(buffer, makeSymbolicFmt, ("&"+varName).c_str(), varName.c_str(), varDeclText.c_str());
        makeSymbolicStmt += "    ";
        makeSymbolicStmt += buffer;

        if (boundary>0 && type->isIntegerType()) {
            sprintf(buffer, upperBoundAssumeFmt, varName.c_str(), (int) boundary);
            makeSymbolicStmt += "    ";
            makeSymbolicStmt += buffer;
            sprintf(buffer, lowerBoundAssumeFmt, varName.c_str(), (int) boundary);
            makeSymbolicStmt += "    ";
            makeSymbolicStmt += buffer;
        }

        return true;
    }

public:
    explicit DriverFuncGenerateVisitor(CompilerInstance *CI)
            : astContext(&(CI->getASTContext())) // initialize private members
    {
        sourceCode.setSourceMgr(astContext->getSourceManager(), astContext->getLangOpts());

        printingPolicy.Bool = 1;
        printingPolicy.ConstantArraySizeAsWritten = 1;

        vars.clear();
        externVariables.clear();
        makeSymbolicStmt = "";

        char buffer[MAX_BUFFER_SIZE];
        makeSymbolicStmt += "    int __nondet__;\n";
        sprintf(buffer, makeSymbolicFmt, "&__nondet__", "__nondet__", "int __nondet__");
        makeSymbolicStmt += "    ";
        makeSymbolicStmt += buffer;
    }

    virtual bool VisitFunctionDecl(FunctionDecl *func) {
        if (func == targetFuncDecl) {
            if (targetFuncName.compare("main")==0) return true;
            for (ParmVarDecl **i=func->param_begin(); i!=func->param_end(); i++) {
                ParmVarDecl *parmVarDecl = *i;
                if (insertSymbolicVar(parmVarDecl->getOriginalType(), parmVarDecl, true)) {
                    vars.insert(parmVarDecl->getNameAsString());
                }
            }
        }

        return true;
    }

    virtual bool VisitDeclRefExpr(DeclRefExpr *declRefExpr) {
        if (!astContext->getSourceManager().isInMainFile(declRefExpr->getLocation())) return true;
        ValueDecl *valueDecl = declRefExpr->getDecl();
        if (VarDecl *varDecl = dyn_cast<VarDecl>(valueDecl)) {
            if (varDecl->hasExternalStorage()) {
                externVariables.insert(varDecl);
            }
            if (GlobalVarSym) {
                if (varDecl->hasGlobalStorage() && varDecl->getStorageClass() != StorageClass::SC_Static) {
                    if (insertSymbolicVar(varDecl->getType(), varDecl, false)) {
                        vars.insert(varDecl->getNameAsString());
                    }
                }
            }
        }
        return true;
    }
};


// visitor 生成kappa stmt
class KappaGenerateVisitor : public RecursiveASTVisitor<KappaGenerateVisitor> {
private:
    ASTContext *astContext;
    int decisionCount;
    int switchCount;
    bool isTargetFunction;

    // 为一个decision生成kappa stmt
    void insertKappaStmt(Expr *decision, SourceLocation declLoc, SourceLocation decisionStartLoc, SourceLocation stmtEndLoc, SourceRange decisionSourceRange, int decisionCount, bool isLoop=false) {
        shared_ptr<LogicExpressionTree> leTree = make_shared<LogicExpressionTree>(decision);
        map<pair<long long, long long>, unsigned int> expect2SeqNum = leTree->getSeqNumMap();

        if (KappaMode == KappaGeneratePolicy::All) {
            triggerNum += expect2SeqNum.size();
            rewriterController->editRewriter(decision, leTree->conditions, leTree->MCCExpect, expect2SeqNum, declLoc, decisionStartLoc, stmtEndLoc, decisionSourceRange, decisionCount, leTree->MCCExpectTrue.size());
        }
        else
#ifndef TRIGGER
            if (KappaMode == KappaGeneratePolicy::Decision && !isLoop) {
            triggerNum += expect2SeqNum.size();
            rewriterController->editRewriter(decision, leTree->conditions, leTree->MCCExpect, expect2SeqNum, declLoc, decisionStartLoc, stmtEndLoc, decisionSourceRange, decisionCount, leTree->MCCExpectTrue.size());
            rewriterController->writeResult();
        } else if (KappaMode == KappaGeneratePolicy::Sequence || isLoop) {
            for (pair<long long, long long> expect : leTree->MCCExpect) {
                triggerNum++;
                rewriterController->editRewriter(decision, leTree->conditions, expect, expect2SeqNum, declLoc, decisionStartLoc, stmtEndLoc, decisionSourceRange, decisionCount, leTree->MCCExpectTrue.size());
                rewriterController->writeResult();
            }
        }
#else
        if (KappaMode == KappaGeneratePolicy::Decision) {
            triggerNum += expect2SeqNum.size();
            rewriterController->editRewriter(decision, leTree->conditions, leTree->MCCExpect, expect2SeqNum, declLoc, decisionStartLoc, stmtEndLoc, decisionSourceRange, decisionCount, leTree->MCCExpectTrue.size(), isLoop);
            rewriterController->writeResult();
        } else if (KappaMode == KappaGeneratePolicy::Sequence) {
            for (pair<long long, long long> expect : leTree->MCCExpect) {
                triggerNum++;
                rewriterController->editRewriter(decision, leTree->conditions, expect, expect2SeqNum, declLoc, decisionStartLoc, stmtEndLoc, decisionSourceRange, decisionCount, leTree->MCCExpectTrue.size());
                rewriterController->writeResult();
            }
        }
#endif
    }

    // 为switch生成kappa stmt
    void insertAssertForSwitchStmt(SwitchStmt *switchStmt, int &switchCount) {
        int caseNum = 0;
        SwitchCase *switchCaseNum = switchStmt->getSwitchCaseList();
        while (NULL != switchCaseNum) {
            switchCaseNum = switchCaseNum->getNextSwitchCase();
            caseNum++;
        }
#ifndef TRIGGER
        char assertFuncName[64] = "klee_assert";
#else
        char triggerFuncName[64] = "klee_trigger_if_false";
        char triggerAndTerminateFuncName[64] = "klee_trigger_and_terminate_if_false";
        char * assertFuncName = (KappaMode==KappaGeneratePolicy::All || (!EarlyStop && KappaMode==KappaGeneratePolicy::Decision))?triggerFuncName:triggerAndTerminateFuncName;
#endif
        char buffer[MAX_BUFFER_SIZE];
        rewriterController->addDecisionText(switchStmt->getSourceRange().getBegin(),
                                            sourceCode.getRewrittenText(switchStmt->getCond()->getSourceRange()));
        SwitchCase *switchCase = switchStmt->getSwitchCaseList();
        while (NULL != switchCase) {
            SwitchAll++;
            triggerNum++;
            if (EnableSpecPath) {
                sprintf(buffer, switchPathRecordStmt, switchPathCount, caseNum--);
            }
            else {
                sprintf(buffer, switchMatchFmt, assertFuncName, switchCount++);
            }
            rewriterController->InsertTextAfter(switchCase->getSubStmt()->getSourceRange().getBegin(), buffer, INDENTATION_NUM);

            switchCase = switchCase->getNextSwitchCase();
        }
        if (KappaMode == KappaGeneratePolicy::Decision || KappaMode == KappaGeneratePolicy::Sequence) {
            rewriterController->writeResult();
        }
        if (EnableSpecPath) {
            switchPathCount++;
        }
    }

public:
    explicit KappaGenerateVisitor(CompilerInstance *CI)
            : astContext(&(CI->getASTContext())), decisionCount(0), switchCount(0), isTargetFunction(false)
    {
        sourceCode.setSourceMgr(astContext->getSourceManager(), astContext->getLangOpts());

        if (KappaMode == KappaGeneratePolicy::All) {
            rewriterController = make_shared<RewriterController>(astContext, MODE_ALL, "MCC");
        }
        else if (KappaMode == KappaGeneratePolicy::Decision) {
            rewriterController = make_shared<RewriterController>(astContext, MODE_DEC, "MCC");
        }
        else if (KappaMode == KappaGeneratePolicy::Sequence) {
            rewriterController = make_shared<RewriterController>(astContext, MODE_SEQ, "MCC");
        }

        printingPolicy.Bool = 1;
        printingPolicy.ConstantArraySizeAsWritten = 1;
    }

    virtual bool VisitFunctionDecl(FunctionDecl *func) {
        if ((func->isThisDeclarationADefinition() && (GenForAllFunc || GenForAllFuncExpectMain)) || func == targetFuncDecl) {
            string funcName = func->getName();
            if (GenForAllFuncExpectMain && funcName.compare("main")==0) {
                isTargetFunction = false;
            }
            else {
                isTargetFunction = true;
                if (func->hasBody()) {
                    Stmt *targetFuncBody = func->getBody();
                    targetFuncEndLoc = targetFuncBody->getSourceRange().getEnd();
                    if (CompoundStmt *compoundStmt = dyn_cast<CompoundStmt>(targetFuncBody)) {
                        if (!compoundStmt->body_empty()) {
                            Stmt *firstStmt = *(compoundStmt->body_begin());
                            targetFuncStartLoc = firstStmt->getSourceRange().getBegin();
                        }
                    }
                }
            }
        }
        else {
            isTargetFunction = false;
        }

        return true;
    }

    virtual bool VisitStmt(Stmt *st) {
        if (!isTargetFunction) return true;
        if (OrigKleeMode) return true;

        SourceRange range = st->getSourceRange();
        if (range.getBegin().isMacroID()) {
            return true;
        }

        if (IfStmt *ifStmt = dyn_cast<IfStmt>(st)) {
            insertKappaStmt(ifStmt->getCond(), targetFuncStartLoc, ifStmt->getSourceRange().getBegin(), targetFuncEndLoc, ifStmt->getCond()->getSourceRange(), decisionCount);
            decisionCount++;
        }
        if (DoStmt *doStmt = dyn_cast<DoStmt>(st)) {
            insertKappaStmt(doStmt->getCond(), targetFuncStartLoc, doStmt->getSourceRange().getBegin(), targetFuncEndLoc, doStmt->getCond()->getSourceRange(), decisionCount, true);
            decisionCount++;
        }
        if (WhileStmt *whileStmt = dyn_cast<WhileStmt>(st)) {
            insertKappaStmt(whileStmt->getCond(), targetFuncStartLoc, whileStmt->getSourceRange().getBegin(), targetFuncEndLoc, whileStmt->getCond()->getSourceRange(), decisionCount, true);
            decisionCount++;
        }
        if (ForStmt *forStmt = dyn_cast<ForStmt>(st)) {
            insertKappaStmt(forStmt->getCond(), targetFuncStartLoc, forStmt->getSourceRange().getBegin(), targetFuncEndLoc, forStmt->getCond()->getSourceRange(), decisionCount, true);
            decisionCount++;
        }
        if (ConditionalOperator *coStmt = dyn_cast<ConditionalOperator>(st)) {
            insertKappaStmt(coStmt->getCond(), targetFuncStartLoc, coStmt->getSourceRange().getBegin(), targetFuncEndLoc, coStmt->getCond()->getSourceRange(), decisionCount);
            decisionCount++;
        }
        if (SwitchStmt *switchStmt = dyn_cast<SwitchStmt>(st)) {
            insertAssertForSwitchStmt(switchStmt, switchCount);
        }

        return true;
    }
};


// visitor 搜索符合名称的函数
class FunctionDeclCollectorVisitor : public RecursiveASTVisitor<FunctionDeclCollectorVisitor> {
private:
    ASTContext *astContext;

public:
    explicit FunctionDeclCollectorVisitor(CompilerInstance *CI)
            : astContext(&(CI->getASTContext())) {
        SourceManager &SM = astContext->getSourceManager();
        sourceCode.setSourceMgr(SM, astContext->getLangOpts());
        funcDeclList.clear();
        targetFuncDecl = NULL;
        hasMain = false;
    }

    virtual bool VisitFunctionDecl(FunctionDecl *func) {
        string funcName = func->getNameInfo().getName().getAsString();
        if (funcName.compare(targetFuncName) == 0) {
            if (func->isThisDeclarationADefinition()) {
                funcDeclList.push_back(func);
            }
        }
        if (func->isMain()) {
            hasMain = true;
            mainFuncDecl = func;
        }
        return true;
    }
};


class KappaGenerateASTConsumer : public ASTConsumer {
private:
    FunctionDeclCollectorVisitor *functionDeclCollectorVisitor;
    DriverFuncGenerateVisitor *driverFuncGenerateVisitor;
    KappaGenerateVisitor *kappaGenerateVisitor; // doesn't have to be private

    // 去除字符串末尾的空格与回车
    string trim(string& str) {
        string::size_type pos = str.find_last_not_of(" \n");
        while (pos != str.size()-1) {
            str.erase(pos + 1);
            pos = str.find_last_not_of(" \n");
        }
        return str;
    }

    // 若该文件夹已存在，则删除，然后按需重建
    void resetSingleDir(string pathString, string subDirName, bool ifReCreat) {
        fs::path rawPath(pathString);
        fs::path fileDir = rawPath.parent_path();
        fileDir /= resultDirStr;
        if (subDirName != "") fileDir /= subDirName;
        if (fs::exists(fileDir)) fs::remove_all(fileDir);
        if (ifReCreat) fs::create_directory(fileDir);
    }

    // 重置输出文件夹
    void resetOutputDir() {
        fs::path rawPath(pathString);
        resultDirStr = "result-" + rawPath.leaf().string();
        resetSingleDir(pathString, "", true);
        resetSingleDir(pathString, KappaSubDirNameStr, true);
        resetSingleDir(pathString, "Statement", statementCoverageOutput);
        resetSingleDir(pathString, "Path", pathCoverageOutput);
    }

public:
    explicit KappaGenerateASTConsumer(CompilerInstance *CI)
            : functionDeclCollectorVisitor(new FunctionDeclCollectorVisitor(CI)),
              driverFuncGenerateVisitor(new DriverFuncGenerateVisitor(CI)),
              kappaGenerateVisitor(new KappaGenerateVisitor(CI))
    {
        langOptions = CI->getLangOpts();
        printingPolicy = PrintingPolicy(langOptions);
    }

    // clang相关主要函数
    virtual void HandleTranslationUnit(ASTContext &Context) {
        // 遍历源代码寻找符合名称的函数
        functionDeclCollectorVisitor->TraverseDecl(Context.getTranslationUnitDecl());
        // 没有找到符合该名称的函数
        if (funcDeclList.size() == 0) {
            llvm::errs() << "ERROR : function named \"" << targetFuncName << "\" not found!\n";
            exit(EXIT_FAILURE);
        }
        // 正好找到了一个符合该名称的函数
        if (funcDeclList.size() == 1) {
            targetFuncDecl = funcDeclList.at(0);
        }
            // 找到了不止一个符合该名称的函数
        else {
            llvm::errs() << "found " << funcDeclList.size() << " functions named " << targetFuncName << ":\n";
            for (unsigned int i=0; i<funcDeclList.size(); i++) {
                string funcSourceText = sourceCode.getRewrittenText(funcDeclList.at(i)->getSourceRange());
                string funcSignText = funcSourceText.substr(0, funcSourceText.find_first_of('{')-1);
                llvm::errs() << "[" << i+1 << "] : " << trim(funcSignText) << "\n";
            }
            llvm::errs() << "please choose one :\n";
            unsigned int funcDeclIdx;
            std::cin >> funcDeclIdx;
            while (funcDeclIdx==0 || funcDeclIdx > funcDeclList.size()) {
                llvm::errs() << "please enter number between 1 and " << funcDeclList.size() << " :\n";
                std::cin >> funcDeclIdx;
            }
            string funcSourceText = sourceCode.getRewrittenText(funcDeclList.at(funcDeclIdx-1)->getSourceRange());
            string funcSignText = funcSourceText.substr(0, funcSourceText.find_first_of('{')-1);
            llvm::errs() << "you choose : " << trim(funcSignText) << "\n";
            targetFuncDecl = funcDeclList.at(funcDeclIdx-1);
        }

        // 遍历源代码生成驱动函数代码
        driverFuncGenerateVisitor->TraverseDecl(Context.getTranslationUnitDecl());
        if (!targetFuncName.compare("main")==0) {
            makeSymbolicStmt += "    "+targetFuncName+"(";
            for (ParmVarDecl **i=targetFuncDecl->param_begin(); i!=targetFuncDecl->param_end(); i++) {
                ParmVarDecl *parmVarDecl = *i;
                makeSymbolicStmt += parmVarDecl->getNameAsString();
                if (i != (targetFuncDecl->param_end()-1)) makeSymbolicStmt += ", ";
            }
            makeSymbolicStmt += ");\n";
        }

        resetOutputDir();
        if (addDriverFunc && (targetFuncName != "main") && hasMain) {
            llvm::errs() << "WARNING :　Already have main function! Driver Function will replace old main function.\n";
        }

        // 遍历源代码生成kappa相关代码
        kappaGenerateVisitor->TraverseDecl(Context.getTranslationUnitDecl());

        // 生成statement coverage所需源文件
        if (statementCoverageOutput) {
            RewriterController statementRewriter(&Context, MODE_NONE, "statement");
            statementRewriter.writeResult();
        }
        // 生成path coverage所需源文件
        if (pathCoverageOutput) {
            RewriterController pathRewriter(&Context, MODE_NONE, "path");
            pathRewriter.writeResult();
        }
    }
};


class KappaGenerateFrontendAction : public ASTFrontendAction {
public:
    KappaGenerateFrontendAction() { }

    void EndSourceFileAction() override {
        if (KappaMode == KappaGeneratePolicy::All) {
            rewriterController->writeResult();
        }
    }

#if CLANG_VERSION == 3
    virtual ASTConsumer *CreateASTConsumer(CompilerInstance &CI, StringRef file) {
        return new KappaGenerateASTConsumer(&CI); // pass CI pointer to ASTConsumer
    }
#else
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                   StringRef file) override {
        return llvm::make_unique<KappaGenerateASTConsumer>(&CI);
    }
#endif
};

shared_ptr<RewriterController> preProcessorRewriterController;

// 添加必要的括号
class PreProcessorVisitor : public RecursiveASTVisitor<PreProcessorVisitor> {
private:
    ASTContext *astContext;
//    bool isFirstStmt;

public:
    explicit PreProcessorVisitor(CompilerInstance *CI)
            : astContext(&(CI->getASTContext())) {
        preProcessorRewriterController = make_shared<RewriterController>(astContext);
    }
//
//    virtual bool VisitFunctionDecl(FunctionDecl *func) {
//        isFirstStmt = true;
//        return true;
//    }

    virtual bool VisitStmt(Stmt *st) {
        SourceRange range = st->getSourceRange();
        if (range.getBegin().isMacroID()) {
            return true;
        }

        if (IfStmt *ifStmt = dyn_cast<IfStmt>(st)) {
            Expr * expr = ifStmt->getCond();
            string decisionText = replaceEnterInStr(preProcessorRewriterController->getRewrittenText(expr->getSourceRange()));
            preProcessorRewriterController->ReplaceText(expr->getSourceRange(), "("+decisionText+")");
        }
//        if (isFirstStmt) {
//            if (CompoundStmt *compoundStmt = dyn_cast<CompoundStmt>(st)) {
//                if (!compoundStmt->body_empty()) {
//                    Stmt *firstStmt = *(compoundStmt->body_begin());
//                    preProcessorRewriterController->InsertTextAfter(firstStmt->getSourceRange().getBegin(), "if (0) (void) 0;\n");
//                }
//            }
//            isFirstStmt = false;
//        }
        return true;
    }
};


class PreProcessorASTConsumer : public ASTConsumer {
private:
    PreProcessorVisitor *preProcessorVisitor;

public:
    explicit PreProcessorASTConsumer(CompilerInstance *CI)
            : preProcessorVisitor(new PreProcessorVisitor(CI))
    { }

    virtual void HandleTranslationUnit(ASTContext &Context) {
        preProcessorVisitor->TraverseDecl(Context.getTranslationUnitDecl());
    }
};


class PreProcessorFrontendAction : public ASTFrontendAction {
public:
    PreProcessorFrontendAction() { }

    void EndSourceFileAction() override {
        SourceManager &SM = preProcessorRewriterController->getSourceMgr();
        pathString = SM.getFileEntryForID(SM.getMainFileID())->getName();
        fs::path rawPath(pathString);
        fs::path fileDir = rawPath.parent_path();

        string fileName = rawPath.filename().string();
        fileDir /= "PreProcessed-"+fileName;
        string pathString = fileDir.string();
        if (fs::exists(fileDir)) fs::remove_all(fileDir);

        preprocessedPathString = "PreProcessed-"+fileName;

#if CLANG_VERSION == 3
        string ErrorInfo;
        llvm::raw_fd_ostream outFile(pathString.c_str(), ErrorInfo, llvm::sys::fs::F_None);
#else
        std::error_code ErrorInfo;
        llvm::raw_fd_ostream outFile(pathString.c_str(), ErrorInfo);
#endif
        preProcessorRewriterController->getEditBuffer(SM.getMainFileID()).write(outFile); // --> this will write the result to outFile
        outFile.close();
    }

#if CLANG_VERSION == 3
    virtual ASTConsumer *CreateASTConsumer(CompilerInstance &CI, StringRef file) {
        return new PreProcessorASTConsumer(&CI); // pass CI pointer to ASTConsumer
    }
#else
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                   StringRef file) override {
        return llvm::make_unique<PreProcessorASTConsumer>(&CI);
    }
#endif
};


// 将files中的文件拷贝到destPath文件夹中，若destPath已存在，则删除重建
void copyTestCaseFiles(vector<fs::path> &files, fs::path &destPath) {
    if (fs::exists(destPath)) fs::remove_all(destPath);
    fs::create_directory(destPath);
    for (fs::path testCaseFile : files) {
        if (fs::is_regular_file(testCaseFile)) {
            string destFileName = testCaseFile.leaf().string();
            string parentDirName = testCaseFile.parent_path().leaf().string();
            string ktestFilePrefix = "test";
            string kleeOutputDirPrefix = "klee-out-";
            destFileName.insert(ktestFilePrefix.length(), "_"+parentDirName.substr(kleeOutputDirPrefix.length(), string::npos)+"_");
            fs::copy_file(testCaseFile, destPath / destFileName);
        }
    }
}

// 从给定的测试用例中挑选
vector<fs::path> selectCoverageTestCase(vector<TestCaseSelector> &testCaseSelectorList,
                                        map<unsigned int, fs::path> &switchTestCaseFile,
                                        vector<map<unsigned int, fs::path> > &validTestCase,
                                        string coverage) {
    vector<fs::path> testCaseFiles;
    for (unsigned int i=0; i<testCaseSelectorList.size(); i++) {
        vector<pair<long long, long long> > seqs;
        if (coverage == "condition") seqs = testCaseSelectorList.at(i).conditionTestCases;
        else if (coverage == "decision") seqs = testCaseSelectorList.at(i).decisionTestCases;
        else if (coverage == "CDC") seqs = testCaseSelectorList.at(i).CDCTestCases;
        else if (coverage == "MCDC") seqs = testCaseSelectorList.at(i).MCDCTestCases;
        for (pair<long long, long long> seq : seqs) {
            unsigned int seqIdx = expect2SeqNumList.at(i)[seq];
            testCaseFiles.push_back(validTestCase.at(i)[seqIdx]);
        }
    }
    for (pair<unsigned int, fs::path> item : switchTestCaseFile)
        testCaseFiles.push_back(item.second);

    return testCaseFiles;
}

// 解析Path字符串，“-”表示一个decision(条件)结束，“^”表示一个switch结束 分隔符都放置在路径值后面
// "|"表示一组path的结束
// 例 T-T-F-X-3^|T-X-T-X-2^|
void parseSpecifiedPath(string SpecPath) {
    specifiedPath.clear();
    switchPath.clear();
    specifiedPathCount = 0;
    switchPathCount = 0;
    pathCount = 0;

    vector<int> oneSpecifiedPath;
    vector<int> oneSwitchPath;

    int path = 0;

    for (int i=0; i<SpecPath.size(); i++) {
        switch (SpecPath[i]) {
            case '|':
                specifiedPath.push_back(oneSpecifiedPath);
                switchPath.push_back(oneSwitchPath);
                oneSpecifiedPath.clear();
                oneSwitchPath.clear();
                pathCount++;
                break;
            case '-': oneSpecifiedPath.push_back(path); path = 0; break;
            case 'T': path = 1; break;
            case 'F': path = 0; break;
            case 'X': path = -1; break;
            case 'P': path = -2; break;
            case '^': oneSwitchPath.push_back(path); path = 0; break;
            case '0':
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9': path = path*10+SpecPath[i]-'0'; break;

            default: llvm::errs() << "[ERROR] Invalid Specified Path!";
        }
    }
}


int main(int argc, const char **argv) {
    struct timeval timeStart;
    gettimeofday(&timeStart,NULL);

#if CLANG_VERSION == 3
    CommonOptionsParser op(argc, argv);
#else
    CommonOptionsParser op(argc, argv, TCGCategory);
#endif
    ClangTool Tool(op.getCompilations(), op.getSourcePathList());

    if ("" != SpecPath) {
        KappaMode = KappaGeneratePolicy::All;
        // 指定路径情况下，其他覆盖率输出flag都无效，但是仍然要至少有一个为true，否则不能正常产生插桩代码
        statementCoverageOutput = false;
        pathCoverageOutput = false;
        MCCOutput = true;
        EnableSpecPath = 1;
        parseSpecifiedPath(SpecPath);
    }

    vector<string> sourcePathList;
#if CLANG_VERSION == 3
    Tool.run(newFrontendActionFactory<PreProcessorFrontendAction>());
    sourcePathList.push_back(preprocessedPathString);
    ClangTool Tool2(op.getCompilations(), sourcePathList);
    Tool2.run(newFrontendActionFactory<KappaGenerateFrontendAction>());
#else
    Tool.run(newFrontendActionFactory<PreProcessorFrontendAction>().get());
    sourcePathList.push_back(preprocessedPathString);
    ClangTool Tool2(op.getCompilations(), sourcePathList);
    Tool2.run(newFrontendActionFactory<KappaGenerateFrontendAction>().get());
#endif

    struct timeval timeCodeGenerationEnd;
    gettimeofday(&timeCodeGenerationEnd,NULL);

    fs::path rawPath(pathString);
    rawPath = rawPath.parent_path();
    rawPath /= resultDirStr;

    string kleeIncludeDir = (KleeIncludePath=="")?"":"-I "+KleeIncludePath+" ";
    string tracerXStr;
    switch (TracerX) {
        case TracerXPolicy::On : tracerXStr = " "; break;
//        case TracerXPolicy::On : tracerXStr = "-debug-subsumption=2 "; break;
        case TracerXPolicy::Off : tracerXStr = "-no-interpolation "; break;
        default : tracerXStr = "";
    }
    string searcherStr;
    switch (TracerX) {
        case TracerXPolicy::On : searcherStr = "-search=dfs "; break;
        case TracerXPolicy::Off : searcherStr = Searcher!=""?"-search="+Searcher+" ":""; break;
        default : searcherStr = Searcher!=""?"-search="+Searcher+" ":"";
    }
    string IgnorePrintfStr = IgnorePrintf?"-ignore-printf ":"";
    string useMergeStr = EnableMerge?"-use-merge ":"";
    // 若启用merge，则interpolation失效
    if (EnableMerge) tracerXStr = "-no-interpolation ";
    string maxTimeStr = MaxTime!=""?"-max-time="+MaxTime+" ":"";
    string maxMemoryStr = MaxMemory!=""?"-max-memory="+MaxMemory+" ":"";

    string maxLoopTimesStr = MaxLoopTimes>=0?"-max-loop-times="+ to_string(MaxLoopTimes)+" ":"";
    string maxLoopForkTimesStr = MaxLoopForkTimes>=0?"-max-loop-fork-times="+ to_string(MaxLoopForkTimes)+" ":"";
    string linkLibStr = "";
    for (const auto &library : LinkLib) {
        linkLibStr += "-link-llvm-lib="+library+" ";
    }

    // 编译生成的代码
    if (runKlee && (conditionCoverageOutput || decisionCoverageOutput || CDCOutput || MCCOutput || MCDCOutput)) {
        string optStr;
        switch (ClangOpt) {
            case ClangOptimizationOption::O_ : optStr = "-O0 "; break;
            case ClangOptimizationOption::O0 : optStr = "-O0 "; break;
            case ClangOptimizationOption::O1 : optStr = "-O1 "; break;
            case ClangOptimizationOption::O2 : optStr = "-O2 "; break;
            case ClangOptimizationOption::O3 : optStr = "-O3 "; break;
            case ClangOptimizationOption::Ofast : optStr = "-Ofast "; break;
            default : optStr = "-O0 ";
        }
        string shellScriptStr =
                "cd "+rawPath.string()+"\n"
                                       "for mode in `ls -1 | grep "+KappaSubDirNameStr+"`; \n"
                                                                                       "do   \n"
                                                                                       "    if [ -d \"$mode\" ]; then\n"
                                                                                       "        cd $mode\n"
                                                                                       "        for sourceFile in `ls -v kappa-*.c`;\n"
                                                                                       "        do\n"
                                                                                       #if CLANG_VERSION > 3
                                                                                       "            "+ClangPath+" "+kleeIncludeDir+"-c -Wno-implicit-function-declaration "+optStr+"-emit-llvm -g $sourceFile\n"
                                                                                       #else
                                                                                       "            "+ClangPath+" "+kleeIncludeDir+"-c -Wno-implicit-function-declaration "+optStr+"-emit-llvm -gline-tables-only $sourceFile\n"
                                                                                                                                                                                   #endif
                                                                                                                                                                                   "        done\n"
                                                                                                                                                                                   "        cd ../\n"
                                                                                                                                                                                   "    fi\n"
                                                                                                                                                                                   "done";

        int returnCode = system(shellScriptStr.c_str());
        if (returnCode==-1) llvm::errs() << "Run Klee ERROR!\n";
    }

    if (statementCoverageOutput) {
        fs::path statementOutputPath = rawPath / "Statement";
        string shellScriptStr =
                "cd "+statementOutputPath.string()+"\n"
                                                   "for sourceFile in `ls -v *.c`;\n"
                                                   "do\n"
                                                   "            "+ClangPath+" "+kleeIncludeDir+"-c -O0 -emit-llvm -g $sourceFile\n"
                                                                                               "done\n";
        int returnCode = system(shellScriptStr.c_str());
        if (returnCode==-1) llvm::errs() << "Run Klee ERROR!\n";
    }

    if (pathCoverageOutput) {
        fs::path statementOutputPath = rawPath / "Path";
        string shellScriptStr =
                "cd "+statementOutputPath.string()+"\n"
                                                   "for sourceFile in `ls -v *.c`;\n"
                                                   "do\n"
                                                   "            "+ClangPath+" "+kleeIncludeDir+"-c -O0 -emit-llvm -g $sourceFile\n"
                                                                                               "done\n";
        int returnCode = system(shellScriptStr.c_str());
        if (returnCode==-1) llvm::errs() << "Run Klee ERROR!\n";
    }

    struct timeval timeCodeCompliedEnd;
    gettimeofday(&timeCodeCompliedEnd,NULL);

    if (KleePrintMode || OrigKleeMode) {
        string emitAllErrorsStr = EmitAllErrors?"-emit-all-errors ":"";
        string optStr = Optimize?"-optimize ":"";
        string shellScriptStr =
                "cd "+rawPath.string()+"\n"
                                       "for mode in `ls -1 | grep "+KappaSubDirNameStr+"`; \n"
                                                                                       "do   \n"
                                                                                       "    if [ -d \"$mode\" ]; then\n"
                                                                                       "        cd $mode\n"
                                                                                       "        for sourceFile in `ls -v kappa-*.c`;\n"
                                                                                       "        do\n"
                                                                                       "            "+KleePath+" -solver-backend=z3 "
                                                                                                               "-dump-states-on-halt=false "
                                                                                                               #if CLANG_VERSION == 3
                                                                                                               "-no-interpolation -allow-external-sym-calls "
                #endif
                +maxLoopTimesStr+maxLoopForkTimesStr+linkLibStr
                +searcherStr+emitAllErrorsStr+optStr+"-only-output-trigger ${sourceFile%.c}.bc >> ../klee_print.msg\n"
                                                     "        done\n"
                                                     "        cd ../\n"
                                                     "    fi\n"
                                                     "done";

        int returnCode = system(shellScriptStr.c_str());
        if (returnCode==-1) llvm::errs() << "Run Klee ERROR!\n";
    } else {
        // 运行klee
        if (runKlee && (conditionCoverageOutput || decisionCoverageOutput || CDCOutput || MCCOutput || MCDCOutput)) {
            string emitAllErrorsStr = EmitAllErrors?"-emit-all-errors ":"";
            // Kappa生成策略为在同一个文件中生成所有decision的Kappa时，需要-emit-all-errors-in-same-path参数保证路径触发断言后不会停止
            string emitAllErrorsInSamePathStr = (KappaMode == KappaGeneratePolicy::All)?"-emit-all-errors-in-same-path ":"";
            string optStr = Optimize?"-optimize ":"";
            string shellScriptStr =
                    "cd "+rawPath.string()+"\n"
                                           "for mode in `ls -1 | grep "+KappaSubDirNameStr+"`; \n"
                                                                                           "do   \n"
                                                                                           "    if [ -d \"$mode\" ]; then\n"
                                                                                           "        cd $mode\n"
                                                                                           "        for sourceFile in `ls -v kappa-*.c`;\n"
                                                                                           "        do\n"
                                                                                           "            triggerNum=$(grep 'klee_trigger' $sourceFile | wc -l)\n"
                                                                                           "            "+KleePath+" -solver-backend=z3 "
                                                                                                                   "-dump-states-on-halt=false "
                                                                                                                   #if CLANG_VERSION == 3
                                                                                                                   "-allow-external-sym-calls "
                                                                                                                   #endif
                                                                                                                   #ifndef TRIGGER
                                                                                                                   +emitAllErrorsInSamePathStr
                                                                                                                   #else
                                                                                                                   "-trigger-times=$triggerNum -only-output-trigger "
                    #endif
                    +maxLoopTimesStr+maxLoopForkTimesStr+linkLibStr
                    +searcherStr+useMergeStr+emitAllErrorsStr+IgnorePrintfStr+tracerXStr+optStr+maxTimeStr+maxMemoryStr+"${sourceFile%.c}.bc\n"
                                                                                                           "        done\n"
                                                                                                           "        cd ../\n"
                                                                                                           "    fi\n"
                                                                                                           "done";

            int returnCode = system(shellScriptStr.c_str());
            if (returnCode==-1) llvm::errs() << "Run Klee ERROR!\n";
        }
    }

    if (statementCoverageOutput) {
        fs::path statementOutputPath = rawPath / "Statement";
        string shellScriptStr =
                "cd "+statementOutputPath.string()+"\n"
                                                   "for sourceFile in `ls -v *.c`;\n"
                                                   "do\n"
                                                   "            "+KleePath+" -solver-backend=z3 --search=dfs "
                                                                           #if CLANG_VERSION == 3
                                                                           "-allow-external-sym-calls -no-interpolation"
                                                                           #endif
                                                                           "-dump-states-on-halt=0 --only-output-states-covering-new "+maxLoopTimesStr+maxLoopForkTimesStr+linkLibStr+IgnorePrintfStr+maxTimeStr+maxMemoryStr+"${sourceFile%.c}.bc\n"
                                                                                                                                                                  "done\n";
        int returnCode = system(shellScriptStr.c_str());
        if (returnCode==-1) llvm::errs() << "Run Klee ERROR!\n";
    }

    if (pathCoverageOutput) {
        fs::path statementOutputPath = rawPath / "Path";
        string shellScriptStr =
                "cd "+statementOutputPath.string()+"\n"
                                                   "for sourceFile in `ls -v *.c`;\n"
                                                   "do\n"
                                                   "            "+KleePath+" -solver-backend=z3 --search=dfs "
                                                                           #if CLANG_VERSION == 3
                                                                           "-allow-external-sym-calls -no-interpolation"
                                                                           #endif
                                                                           "-dump-states-on-halt=0 "+maxLoopTimesStr+maxLoopForkTimesStr+linkLibStr+IgnorePrintfStr+maxTimeStr+maxMemoryStr+"${sourceFile%.c}.bc\n"
                                                                                                                                "done\n";
        int returnCode = system(shellScriptStr.c_str());
        if (returnCode==-1) llvm::errs() << "Run Klee ERROR!\n";
    }

    struct timeval timeKleeEnd;
    gettimeofday(&timeKleeEnd,NULL);

    if (EnableSpecPath) return 0;

    string coverageMessage;
    double timeUsedForSelect = 0;
    if (conditionCoverageOutput || decisionCoverageOutput || CDCOutput || MCCOutput || MCDCOutput) {
        vector<map<unsigned int, fs::path> > validTestCase;
        for (unsigned int i=0; i<conditionTextList.size(); i++) {
            validTestCase.push_back(map<unsigned int, fs::path>());
        }
        map<unsigned int, fs::path> switchTestCaseFile;

#ifndef TRIGGER
        boost::regex seqIdxReg("Error: ASSERTION FAIL: __kappa__(.+)__ != __expect__(.+)__(.+)__(.+)__");
        boost::regex switchSeqIdxReg("Error: ASSERTION FAIL: (.+)\\*0");
        string fileSuffix = ".assert.err";
#else
        boost::regex seqIdxReg("Error: TRIGGER: __kappa__(.+)__ != __expect__(.+)__(.+)__(.+)__");
        boost::regex switchSeqIdxReg("Error: TRIGGER: (.+)\\*0");
        string fileSuffix = ".trigger.err";
#endif

        // 分析符号执行的结果，提取出其中需要的测试用例组成测试用例集
        fs::path MCCResultPath = rawPath;
        MCCResultPath /= KappaSubDirNameStr;
        fs::directory_iterator end_iter;
        for (fs::directory_iterator iter(MCCResultPath); iter!=end_iter; iter++) {
            if (!fs::is_directory(iter->status())) continue;
            fs::path kleeOutputDir = iter->path();
            // 寻找klee输出结果文件夹
            if (kleeOutputDir.leaf().string().find("klee-out-") == string::npos) continue;
            for (fs::directory_iterator iter(kleeOutputDir); iter!=end_iter; iter++) {
                if (!fs::is_regular_file(iter->status())) continue;
                fs::path testCaseInfo = iter->path();
                string testCaseInfoPathString = testCaseInfo.leaf().string();
                // 寻找由于断言错误产生的测试用例
                if (testCaseInfoPathString.find(fileSuffix) == string::npos) continue;
                std::ifstream ifs(testCaseInfo.string());
                string testCaseInfoStr;
                getline(ifs, testCaseInfoStr);

                boost::sregex_token_iterator endIter;

                // switch测试用例
                boost::sregex_token_iterator switchIdxIter(
                        testCaseInfoStr.cbegin(), testCaseInfoStr.cend(), switchSeqIdxReg, 1);
                if (switchIdxIter != endIter) {
                    fs::path testCasePath = kleeOutputDir;
                    testCasePath /= testCaseInfoPathString.substr(0, testCaseInfoPathString.rfind(fileSuffix))+".ktest";
                    string switchIdxStr = *switchIdxIter;
                    int switchIdx = atoi(switchIdxStr.c_str());
                    switchTestCaseFile.insert(make_pair(switchIdx, testCasePath));
                    SwitchGen++;
                    continue;
                }

                // if/for/while/do测试用例
                boost::sregex_token_iterator decisionIdxIter(
                        testCaseInfoStr.cbegin(), testCaseInfoStr.cend(), seqIdxReg, 1);
                boost::sregex_token_iterator seqIdxIter(
                        testCaseInfoStr.cbegin(), testCaseInfoStr.cend(), seqIdxReg, 4);
                if (seqIdxIter != endIter) {
                    fs::path testCasePath = kleeOutputDir;
                    testCasePath /= testCaseInfoPathString.substr(0, testCaseInfoPathString.rfind(fileSuffix))+".ktest";
                    string decisionIdxStr = *decisionIdxIter;
                    string seqIdxStr = *seqIdxIter;
                    int decisionIdx = atoi(decisionIdxStr.c_str());
                    int seqIdx = atoi(seqIdxStr.c_str());
                    validTestCase.at(decisionIdx).insert(make_pair(seqIdx, testCasePath));
                }
            }
        }

        int caseNum = 0;
        if (KleePrintMode) {
            boost::regex seqIdxReg("\\{\"Kappa(.+)\":(.+), \"size\":(.+), \"result\":(.+)\\}");

            fs::path KleePrintResultPath = rawPath;
            KleePrintResultPath /= "klee_print.msg";
            std::ifstream ifs(KleePrintResultPath.string());

            string testCaseInfoStr;
            while (getline(ifs, testCaseInfoStr)) {
                caseNum++;
                boost::sregex_token_iterator endIter;

                boost::sregex_token_iterator decisionIdxIter(
                        testCaseInfoStr.cbegin(), testCaseInfoStr.cend(), seqIdxReg, 1);
                boost::sregex_token_iterator seqIdxIter(
                        testCaseInfoStr.cbegin(), testCaseInfoStr.cend(), seqIdxReg, 2);
                if (seqIdxIter != endIter) {
                    string decisionIdxStr = *decisionIdxIter;
                    string seqIdxStr = *seqIdxIter;
                    int decisionIdx = atoi(decisionIdxStr.c_str());
                    int seqIdx = atoi(seqIdxStr.c_str());
                    validTestCase.at(decisionIdx).insert(make_pair(seqIdx, "xxx"));
                }
            }

        }

        // 通过TestCaseSelector类计算符合覆盖率的测试用例集
        vector<TestCaseSelector> testCaseSelectorList;
        for (unsigned int i=0; i<validTestCase.size(); i++) {
            vector<pair<long long, long long> > trueTestCase, falseTestCase;
            vector<string> testCaseFileNameList;
            for (pair<unsigned int, fs::path> testCase : validTestCase.at(i)) {
                if (KleePrintMode) {
                    for (auto item : trueSeqNum2ExpectList.at(i)) {
                        if (item.second.first == testCase.first)
                            trueTestCase.push_back(item.second);
                    }
                    for (auto item : falseSeqNum2ExpectList.at(i)) {
                        if (item.second.first == testCase.first)
                            falseTestCase.push_back(item.second);
                    }
                } else {
                    if (trueSeqNum2ExpectList.at(i).count(testCase.first))
                        trueTestCase.push_back(trueSeqNum2ExpectList.at(i).at(testCase.first));
                    else
                        falseTestCase.push_back(falseSeqNum2ExpectList.at(i).at(testCase.first));
                }

                fs::path testCaseFile = testCase.second;
                if (fs::is_regular_file(testCaseFile)) {
                    string destFileName = testCaseFile.leaf().string();
                    string parentDirName = testCaseFile.parent_path().leaf().string();
                    string ktestFilePrefix = "test";
                    string kleeOutputDirPrefix = "klee-out-";
                    destFileName.insert(ktestFilePrefix.length(), "_"+parentDirName.substr(kleeOutputDirPrefix.length(), string::npos)+"_");
                    testCaseFileNameList.push_back(destFileName);
                }
                else testCaseFileNameList.push_back("");
            }

#define getTimeUsed(timeEnd, timeStart) (timeEnd.tv_sec - timeStart.tv_sec) + (double)(timeEnd.tv_usec - timeStart.tv_usec)/1000000.0
            struct timeval beforeSelect;
            gettimeofday(&beforeSelect,NULL);
            TestCaseSelector testCaseSelector(trueTestCase, falseTestCase, conditionTextList.at(i), decisionTextList.at(i), testCaseFileNameList, true, expect2SeqNumList.at(i).size());
            testCaseSelectorList.push_back(testCaseSelector);
            struct timeval afterSelect;
            gettimeofday(&afterSelect,NULL);
            timeUsedForSelect += getTimeUsed(afterSelect, beforeSelect);
#undef getTimeUsed
        }

        llvm::errs() << "Result :\n";
        // 根据选择的测试用例将对应的ktest文件复制到输出目录
        if (decisionCoverageOutput) {
            vector<fs::path> testCaseFiles = selectCoverageTestCase(testCaseSelectorList, switchTestCaseFile, validTestCase, "decision");
            fs::path outputPath = rawPath / "Decision";
            copyTestCaseFiles(testCaseFiles, outputPath);
            string decisionCoverageStr = formatDoubleValue((double)decisionGen*100/decisionAll, 2);
            caseNumDecision = testCaseFiles.size();
            llvm::errs() << "Decision Coverage : " << decisionCoverageStr << "%  (" << to_string(decisionGen) << "/" << to_string(decisionAll) << ")\n";
            coverageMessage += "Decision Coverage : "+decisionCoverageStr+"%  ("+ to_string(decisionGen)+"/"+ to_string(decisionAll)+")\n";
        }
        if (conditionCoverageOutput) {
            vector<fs::path> testCaseFiles = selectCoverageTestCase(testCaseSelectorList, switchTestCaseFile, validTestCase, "condition");
            fs::path outputPath = rawPath / "Condition";
            copyTestCaseFiles(testCaseFiles, outputPath);
            caseNumCondition = testCaseFiles.size();
            string conditionCoverageStr = formatDoubleValue((double)conditionGen*100/conditionAll, 2);
            llvm::errs() << "Condition Coverage : " << conditionCoverageStr << "%  (" << to_string(conditionGen) << "/" << to_string(conditionAll) << ")\n";
            coverageMessage += "Condition Coverage : "+conditionCoverageStr+"%  ("+ to_string(conditionGen)+"/"+ to_string(conditionAll)+")\n";
        }
        if (CDCOutput) {
            vector<fs::path> testCaseFiles = selectCoverageTestCase(testCaseSelectorList, switchTestCaseFile, validTestCase, "CDC");
            fs::path outputPath = rawPath / "CDC";
            copyTestCaseFiles(testCaseFiles, outputPath);
            caseNumCDC = testCaseFiles.size();
            string CDCStr = formatDoubleValue((double)CDCGen*100/CDCAll, 2);
            llvm::errs() << "CDC : " << CDCStr << "%  (" << to_string(CDCGen) << "/" << to_string(CDCAll) << ")\n";
            coverageMessage += "CDC : "+CDCStr+"%  ("+ to_string(CDCGen)+"/"+ to_string(CDCAll)+")\n";
        }
        if (MCDCOutput) {
            vector<fs::path> testCaseFiles = selectCoverageTestCase(testCaseSelectorList, switchTestCaseFile, validTestCase, "MCDC");
            fs::path outputPath = rawPath / "MCDC";
            copyTestCaseFiles(testCaseFiles, outputPath);
            caseNumMCDC = testCaseFiles.size();
            string MCDCStr = formatDoubleValue((double)MCDCGen*100/MCDCAll, 2);
            llvm::errs() << "MCDC : " << MCDCStr << "%  (" << to_string(MCDCGen) << "/" << to_string(MCDCAll) << ")\n";
            coverageMessage += "MCDC : "+MCDCStr+"%  ("+ to_string(MCDCGen)+"/"+ to_string(MCDCAll)+")\n";
        }
        if (MCCOutput) {
            vector<fs::path> testCaseFiles;
            for (map<unsigned int, fs::path> validTestCaseEachDecision : validTestCase)
                for (pair<unsigned int, fs::path> item : validTestCaseEachDecision)
                    testCaseFiles.push_back(item.second);
            for (pair<unsigned int, fs::path> item : switchTestCaseFile)
                testCaseFiles.push_back(item.second);

            fs::path outputPath = rawPath / "MCC";
            copyTestCaseFiles(testCaseFiles, outputPath);
            caseNumMCC = testCaseFiles.size();
            string MCCStr = formatDoubleValue((double)MCCGen*100/MCCAll, 2);
            llvm::errs() << "MCC : " << MCCStr << "%  (" << to_string(MCCGen) << "/" << to_string(MCCAll) << ")\n";
            coverageMessage += "MCC : "+MCCStr+"%  ("+ to_string(MCCGen)+"/"+ to_string(MCCAll)+")\n";
        }
        if (SwitchAll != 0) {
            string SwitchStr = formatDoubleValue((double)SwitchGen*100/SwitchAll, 2);
            llvm::errs() << "Switch : " << SwitchStr << "%  (" << to_string(SwitchGen) << "/" << to_string(SwitchAll) << ")\n";
            coverageMessage += "Switch : "+SwitchStr+"%  ("+ to_string(SwitchGen)+"/"+ to_string(SwitchAll)+")\n";
        }

        if (KleePrintMode) {
            caseNumCondition = caseNum;
            caseNumDecision = caseNum;
            caseNumCDC = caseNum;
            caseNumMCC = caseNum;
            caseNumMCDC = caseNum;
        }

        if (OrigKleeCov) {
            if (decisionCoverageOutput) {
                string decisionCoverageStr = formatDoubleValue((double)KdecisionGen*100/KdecisionAll, 2);
                llvm::errs() << "KLEE Decision Coverage : " << decisionCoverageStr << "%  (" << to_string(KdecisionGen) << "/" << to_string(KdecisionAll) << ")\n";
                coverageMessage += "KLEE Decision Coverage : "+decisionCoverageStr+"%  ("+ to_string(KdecisionGen)+"/"+ to_string(KdecisionAll)+")\n";
            }
            if (conditionCoverageOutput) {
                string conditionCoverageStr = formatDoubleValue((double)KconditionGen*100/KconditionAll, 2);
                llvm::errs() << "Condition Coverage : " << conditionCoverageStr << "%  (" << to_string(KconditionGen) << "/" << to_string(KconditionAll) << ")\n";
                coverageMessage += "KLEE Condition Coverage : "+conditionCoverageStr+"%  ("+ to_string(KconditionGen)+"/"+ to_string(KconditionAll)+")\n";
            }
            if (CDCOutput) {
                string CDCStr = formatDoubleValue((double)KCDCGen*100/KCDCAll, 2);
                llvm::errs() << "KLEE CDC : " << CDCStr << "%  (" << to_string(KCDCGen) << "/" << to_string(KCDCAll) << ")\n";
                coverageMessage += "KLEE CDC : "+CDCStr+"%  ("+ to_string(KCDCGen)+"/"+ to_string(KCDCAll)+")\n";
            }
            if (MCDCOutput) {
                string MCDCStr = formatDoubleValue((double)KMCDCGen*100/KMCDCAll, 2);
                llvm::errs() << "KLEE MCDC : " << MCDCStr << "%  (" << to_string(KMCDCGen) << "/" << to_string(KMCDCAll) << ")\n";
                coverageMessage += "KLEE MCDC : "+MCDCStr+"%  ("+ to_string(KMCDCGen)+"/"+ to_string(KMCDCAll)+")\n";
            }
            if (MCCOutput) {
                string MCCStr = formatDoubleValue((double)KMCCGen*100/KMCCAll, 2);
                llvm::errs() << "KLEE MCC : " << MCCStr << "%  (" << to_string(KMCCGen) << "/" << to_string(KMCCAll) << ")\n";
                coverageMessage += "KLEE MCC : "+MCCStr+"%  ("+ to_string(KMCCGen)+"/"+ to_string(KMCCAll)+")\n";
            }
        }
    }

    struct timeval timeAllEnd;
    gettimeofday(&timeAllEnd,NULL);

#define getTimeUsed(timeEnd, timeStart) (timeEnd.tv_sec - timeStart.tv_sec) + (double)(timeEnd.tv_usec - timeStart.tv_usec)/1000000.0
    string totalTimeStr = "Total time(sec)     : "+formatDoubleValue(getTimeUsed(timeAllEnd, timeStart), 6)+"\n";
    string preProcessTimeStr = "PreProcess time(sec)  : "+formatDoubleValue(getTimeUsed(timeCodeGenerationEnd, timeStart), 6)+"\n";
    string clangTimeStr = "Clang time(sec)  : "+formatDoubleValue(getTimeUsed(timeCodeCompliedEnd, timeCodeGenerationEnd), 6)+"\n";
    string kleeTimeStr = "KLEE time(sec)      : "+formatDoubleValue(getTimeUsed(timeKleeEnd, timeCodeCompliedEnd), 6)+"\n";
    string postProcessTimeStr = "PostProcess time(sec) : "+formatDoubleValue(getTimeUsed(timeAllEnd, timeKleeEnd), 6)+"\n";
    string selectTimeStr = "Select time(sec) : "+formatDoubleValue(timeUsedForSelect, 6)+"\n";

    llvm::errs() << "\n" << totalTimeStr << preProcessTimeStr << clangTimeStr << kleeTimeStr << postProcessTimeStr << "\n";

    string jsonMessage = "";
    jsonMessage += "{\"Total time\":"+formatDoubleValue(getTimeUsed(timeAllEnd, timeStart), 6)
            +", \"PreProcess time\":"+formatDoubleValue(getTimeUsed(timeCodeGenerationEnd, timeStart), 6)
            +", \"Clang time\":"+formatDoubleValue(getTimeUsed(timeCodeCompliedEnd, timeCodeGenerationEnd), 6)
            +", \"KLEE time\":"+formatDoubleValue(getTimeUsed(timeKleeEnd, timeCodeCompliedEnd), 6)
            +", \"PostProcess time\":"+formatDoubleValue(getTimeUsed(timeAllEnd, timeKleeEnd), 6)
            +", \"Select time\":"+formatDoubleValue(timeUsedForSelect, 6)
            +", \"Decision\":"+formatDoubleValue((double)decisionGen*100/decisionAll, 2)
            +", \"Condition\":"+formatDoubleValue((double)conditionGen*100/conditionAll, 2)
            +", \"CDC\":"+formatDoubleValue((double)CDCGen*100/CDCAll, 2)
            +", \"MCC\":"+formatDoubleValue((double)MCCGen*100/MCCAll, 2)
            +", \"MCDC\":"+formatDoubleValue((double)MCDCGen*100/MCDCAll, 2)
            +", \"Decision Gen\":"+to_string(decisionGen)
            +", \"Condition Gen\":"+to_string(conditionGen)
            +", \"CDC Gen\":"+to_string(CDCGen)
            +", \"MCC Gen\":"+to_string(MCCGen)
            +", \"MCDC Gen\":"+to_string(MCDCGen)
            +", \"Decision All\":"+to_string(decisionAll)
            +", \"Condition All\":"+to_string(conditionAll)
            +", \"CDC All\":"+to_string(CDCAll)
            +", \"MCC All\":"+to_string(MCCAll)
            +", \"MCDC All\":"+to_string(MCDCAll)
            +", \"Decision Case Num\":"+to_string(caseNumDecision)
            +", \"Condition Case Num\":"+to_string(caseNumCondition)
            +", \"CDC Case Num\":"+to_string(caseNumCDC)
            +", \"MCC Case Num\":"+to_string(caseNumMCC)
            +", \"MCDC Case Num\":"+to_string(caseNumMCDC);
    if (OrigKleeCov) {
        jsonMessage += ", \"KLEE Decision\":"+formatDoubleValue((double)KdecisionGen*100/KdecisionAll, 2)
                       +", \"KLEE Condition\":"+formatDoubleValue((double)KconditionGen*100/KconditionAll, 2)
                       +", \"KLEE CDC\":"+formatDoubleValue((double)KCDCGen*100/KCDCAll, 2)
                       +", \"KLEE MCC\":"+formatDoubleValue((double)KMCCGen*100/KMCCAll, 2)
                       +", \"KLEE MCDC\":"+formatDoubleValue((double)KMCDCGen*100/KMCDCAll, 2)
                       +", \"KLEE Decision Gen\":"+to_string(KdecisionGen)
                       +", \"KLEE Condition Gen\":"+to_string(KconditionGen)
                       +", \"KLEE CDC Gen\":"+to_string(KCDCGen)
                       +", \"KLEE MCC Gen\":"+to_string(KMCCGen)
                       +", \"KLEE MCDC Gen\":"+to_string(KMCDCGen);
    }
    jsonMessage += "}\n";
#undef getTimeUsed

    fs::path messageOutPath = rawPath / "message.txt";
    ofstream fOut(messageOutPath.string());
    fOut << jsonMessage << "\n\n";
    fOut << coverageMessage << "\n\n";
    fOut << totalTimeStr << preProcessTimeStr << clangTimeStr << kleeTimeStr << postProcessTimeStr << selectTimeStr << "\n\n";
    fOut << messageStr << "\n\n";
    fOut.close();
    std::cout << kleeTimeStr;

    return 0;
}
