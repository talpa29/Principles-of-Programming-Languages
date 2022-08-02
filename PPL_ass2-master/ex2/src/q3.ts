import { map, zipWith } from "ramda";
import { AppExp, CExp, Exp, LetExp, makeLetExp, makeLetPlusExp, Program }  from "./L31-ast";
import {isVarRef, isPrimOp, isBoolExp,isNumExp,isAppExp, isAtomicExp, isCExp, isDefineExp, isExp, isIfExp, isLetExp, isLitExp,
         isProcExp, isProgram, makeAppExp, makeDefineExp, makeIfExp, makeProcExp, makeProgram,makeBinding,Binding,isLetPlusExp, LetPlusExp }  from "./L31-ast";
import { Result, bind, makeFailure, makeOk, mapResult, safe2, mapv } from "../shared/result";
import { makeBox } from "../shared/box";



export const rewriteLetPlusCExp = (e: LetPlusExp): Result<CExp> => {
    const vars = map((b) => b.var, e.bindings);
    const vals = map((b) => b.val, e.bindings);
    const exp = rewriteLetPlus(e);
    return safe2((bindings: CExp[], body: CExp[]) => makeOk(makeLetExp(zipWith(makeBinding,map(binding => binding.var.var, exp.bindings),bindings),body)))
                            (mapResult((binding : Binding ) => rewriteAllLetPlusCExp(binding.val), exp.bindings),
                            mapResult(rewriteAllLetPlusCExp, exp.body))
}

export const rewriteLetPlus = (e: LetPlusExp): LetExp => {
    if (e.bindings.length == 1) {
        return makeLetExp(e.bindings, e.body);
    }
    return makeLetExp(e.bindings.slice(0,1), makeBox(makeLetPlusExp(e.bindings.slice(1),e.body)));
}


/*
Purpose: Transform L31 AST to L3 AST
Signature: l31ToL3(l31AST)
Type: [Exp | Program] => Result<Exp | Program>
*/
export const L31ToL3 = (exp: Exp | Program): Result<Exp | Program> =>
isProgram(exp) ? bind(mapResult(rewriteAllLetPlusExp, exp.exps),(exp: Exp[]) => makeOk(makeProgram(exp))) :
isExp(exp) ? rewriteAllLetPlusExp(exp) :
makeFailure("Failure");

const rewriteAllLetPlusExp = (exp: Exp): Result<Exp> =>
    isDefineExp(exp) ? bind(rewriteAllLetPlusCExp(exp.val), (val: CExp) => makeOk(makeDefineExp(exp.var, val))):
    rewriteAllLetPlusCExp(exp);

const rewriteAllLetPlusCExp = (exp: CExp): Result<CExp>=>
    isAtomicExp(exp) ? makeOk(exp) :
    isNumExp(exp) ? makeOk(exp) :
    isBoolExp(exp) ? makeOk(exp) :
    isPrimOp(exp) ? makeOk(exp) :
    isVarRef(exp) ? makeOk(exp) :
    isLitExp(exp) ? makeOk(exp) :
    isIfExp(exp) ? bind(rewriteAllLetPlusCExp(exp.test), test => (bind(rewriteAllLetPlusCExp(exp.then), then => bind(rewriteAllLetPlusCExp(exp.alt), alt => makeOk( makeIfExp(test,then,alt)))))) :
    isAppExp(exp) ? safe2((rator: CExp, rands: CExp[])=> makeOk(makeAppExp(exp.rator,exp.rands)))
                            (rewriteAllLetPlusCExp(exp.rator), mapResult(rewriteAllLetPlusCExp, exp.rands)):                      
    isProcExp(exp) ? bind(mapResult(rewriteAllLetPlusCExp, exp.body), (body: CExp[]) => makeOk(makeProcExp(exp.args,body))):
    isLetExp(exp) ? safe2((bindings: CExp[], body: CExp[]) => makeOk(makeLetExp(zipWith(makeBinding,map(binding => binding.var.var, exp.bindings),bindings),body)))
                            (mapResult((binding : Binding ) => rewriteAllLetPlusCExp(binding.val), exp.bindings),
                            mapResult(rewriteAllLetPlusCExp, exp.body)):
    isLetPlusExp(exp) ? rewriteLetPlusCExp(exp) :
     makeFailure("error");





    

