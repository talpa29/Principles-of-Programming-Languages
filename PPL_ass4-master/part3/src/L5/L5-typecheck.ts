// L5-typecheck
// ========================================================
import {  equals, filter, flatten, includes, map, intersection, zipWith, reduce, is, slice } from 'ramda';
import { isAppExp, isBoolExp, isDefineExp, isIfExp, isLetrecExp, isLetExp, isNumExp,
         isPrimOp, isProcExp, isProgram, isStrExp, isVarRef, unparse, parseL51,
         AppExp, BoolExp, DefineExp, Exp, IfExp, LetrecExp, LetExp, NumExp, SetExp, LitExp,
         Parsed, PrimOp, ProcExp, Program, StrExp, isSetExp, isLitExp, 
         isDefineTypeExp, isTypeCaseExp, DefineTypeExp, TypeCaseExp, CaseExp, makeSetExp, isCaseExp, makeVarRef, VarRef, CExp, makeAppExp } from "./L5-ast";
import { applyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv } from "./TEnv";
import { isProcTExp, makeBoolTExp, makeNumTExp, makeProcTExp, makeStrTExp, makeVoidTExp,
         parseTE, unparseTExp, Record,
         BoolTExp, NumTExp, StrTExp, TExp, VoidTExp, UserDefinedTExp, isUserDefinedTExp, UDTExp, 
         isNumTExp, isBoolTExp, isStrTExp, isVoidTExp,
         isRecord, ProcTExp, makeUserDefinedNameTExp, Field, makeAnyTExp, isAnyTExp, isUserDefinedNameTExp, parseTExp, makeUserDefinedTExp, isField, isTVar, tvarContents, tvarIsNonEmpty, tvarSetContents } from "./TExp";
import { isEmpty, allT, first, rest, cons } from '../shared/list';
import { Result, makeFailure, bind, makeOk, zipWithResult, mapv, mapResult, isFailure, either, isOk, safe2 } from '../shared/result';
import { isEmptySExp, makeSymbolSExp, isSymbolSExp } from './L5-value';
import { isCompoundSexp } from '../shared/parser';
import { makeExtEnv } from './L5-env';
import {parse} from '../shared/parser'
import { env } from 'process';
import { checkNoOccurrence } from './L5-substitution-adt';


// L51
export const getTypeDefinitions = (p: Program): UserDefinedTExp[] => {
    const iter = (head: Exp, tail: Exp[]): UserDefinedTExp[] =>
        isEmpty(tail) && isDefineTypeExp(head) ? [head.udType] :
        isEmpty(tail) ? [] :
        isDefineTypeExp(head) ? cons(head.udType, iter(first(tail), rest(tail))) :
        iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getDefinitions = (p: Program): DefineExp[] => {
    const iter = (head: Exp, tail: Exp[]): DefineExp[] =>
        isEmpty(tail) && isDefineExp(head) ? [head] :
        isEmpty(tail) ? [] :
        isDefineExp(head) ? cons(head, iter(first(tail), rest(tail))) :
        iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getRecords = (p: Program): Record[] =>
    flatten(map((ud: UserDefinedTExp) => ud.records, getTypeDefinitions(p)));

// L51
export const getItemByName = <T extends {typeName: string}>(typeName: string, items: T[]): Result<T> => {
    return isEmpty(items) ? makeFailure(`${typeName} not found`) :
    first(items).typeName === typeName ? makeOk(first(items)) :
    getItemByName(typeName, rest(items));
}
    

// L51
export const getUserDefinedTypeByName = (typeName: string, p: Program): Result<UserDefinedTExp> =>
    getItemByName(typeName, getTypeDefinitions(p));

// L51
export const getRecordByName = (typeName: string, p: Program): Result<Record> =>
    getItemByName(typeName, getRecords(p));

// L51
// Given the name of record, return the list of UD Types that contain this record as a case.
export const getRecordParents = (typeName: string, p: Program): UserDefinedTExp[] =>
    filter((ud: UserDefinedTExp): boolean => map((rec: Record) => rec.typeName, ud.records).includes(typeName),
        getTypeDefinitions(p));


// L51
// Given a user defined type name, return the Record or UD Type which it names.
// (Note: TS fails to type check either in this case)
export const getTypeByName = (typeName: string, p: Program): Result<UDTExp> => {
    const ud = getUserDefinedTypeByName(typeName, p);
    if (isFailure(ud)) {
        return getRecordByName(typeName, p);
    } else {
        return ud;
    }
}

// TODO L51
// Is te1 a subtype of te2?
const isSubType = (te1: TExp | undefined, te2: TExp, p: Program): boolean => {
    if(isAnyTExp(te2)) {
        return true
    }
    else if(isUserDefinedNameTExp(te1) && isUserDefinedNameTExp(te2)) {
        const UD = getUserDefinedTypeByName(te2.typeName,p)

        return isOk(UD) ? getRecordParents(te1.typeName,p).includes(UD.value) : false
    }
    else {
        return false
    }
}
    
    


// TODO L51: Change this definition to account for user defined types
// Purpose: Check that the computed type te1 can be accepted as an instance of te2
// test that te1 is either the same as te2 or more specific
// Deal with case of user defined type names 
// Exp is only passed for documentation purposes.
// p is passed to provide the context of all user defined types
export const checkEqualType = (te1: TExp, te2: TExp, exp: Exp, p: Program): Result<TExp> => {    
    return equals(te1, te2) ? makeOk(te2) :
    isSubType(te1,te2,p) ? makeOk(te2) :
    makeFailure(`Incompatible types: ${te1} and ${te2} in ${exp}`);
}
    


// L51
// Return te and its parents in type hierarchy to compute type cover
// Return type names (not their definition)
export const getParentsType = (te: TExp, p: Program): TExp[] =>
    (isNumTExp(te) || isBoolTExp(te) || isStrTExp(te) || isVoidTExp(te) || isAnyTExp(te)) ? [te] :
    isProcTExp(te) ? [te] :
    isUserDefinedTExp(te) ? [te] :
    isRecord(te) ? getParentsType(makeUserDefinedNameTExp(te.typeName), p) :
    isUserDefinedNameTExp(te) ?
        either(getUserDefinedTypeByName(te.typeName, p),
                (ud: UserDefinedTExp) => [makeUserDefinedNameTExp(ud.typeName)],
                (_) => either(getRecordByName(te.typeName, p),
                            (rec: Record) => cons(makeUserDefinedNameTExp(rec.typeName), 
                                                  map((ud) => makeUserDefinedNameTExp(ud.typeName), 
                                                      getRecordParents(rec.typeName, p))),
                            (_) => [])) : 
    [];

// L51
// Get the list of types that cover all ts in types.
export const coverTypes = (types: TExp[], p: Program): TExp[] => 
    // [[p11, p12], [p21], [p31, p32]] --> types in intersection of all lists
    ((parentsList: TExp[][]): TExp[] => reduce<TExp[], TExp[]>(intersection, first(parentsList), rest(parentsList)))
     (map((t) => getParentsType(t,p), types));

// Return the most specific in a list of TExps
// For example given UD(R1, R2):
// - mostSpecificType([R1, R2, UD]) = R1 (choses first out of record level)
// - mostSpecificType([R1, number]) = number  
export const mostSpecificType = (types: TExp[], p: Program): TExp =>
    reduce((min: TExp, element: TExp) => isSubType(element, min, p) ? element : min, 
            makeAnyTExp(),
            types);
    // types.reduce((acc: TExp,cur: TExp) => isSubType(cur,acc,p) ? cur : acc)

// L51
// Check that all t in types can be covered by a single parent type (not by 'any')
// Return most specific parent
export const checkCoverType = (types: TExp[], p: Program): Result<TExp> => {
    const cover = coverTypes(types, p);
    return isEmpty(cover) ? makeFailure(`No type found to cover ${map((t) => JSON.stringify(unparseTExp(t), null, 2), types).join(" ")}`) :
    makeOk(mostSpecificType(cover, p));
}


// Compute the initial TEnv given user defined types
// =================================================
// TODO L51
// Construct type environment for the user-defined type induced functions
// Type constructor for all records
// Type predicate for all records
// Type predicate for all user-defined-types
// All globally defined variables (with define)

// TODO: Define here auxiliary functions for TEnv computation

// TOODO L51
// Initialize TEnv with:
// * Type of global variables (define expressions at top level of p)
// * Type of implicitly defined procedures for user defined types (define-type expressions in p)


export const initTEnv = (p: Program): TEnv => {
    const env = makeEmptyTEnv()
    const records = getRecords(p)
    const names_Records = map((x: Record) => x.typeName ,getRecords(p))
    const env2 = makeExtendTEnv(names_Records,getRecords(p),env)
    const names_UD = map((x : UserDefinedTExp) => x.typeName, getTypeDefinitions(p))
    const env3 = makeExtendTEnv(names_UD,getTypeDefinitions(p),env2)    

    const make_func_names: string[] = map((rec_name) => `make-${rec_name}`,names_Records)
    const make_func_types = mapResult((rec) => bind(parse(fieldsTostringType(rec)), (exp) => parseTExp(exp,names_Records)) ,records)
    const envt = isOk(make_func_types) ? makeExtendTEnv(make_func_names,make_func_types.value,env3) : makeEmptyTEnv()

    const question_names: string[] = map((rec_name) => `${rec_name}?`,names_Records)
    const question_func_types = mapResult((rec) => parseTE('(any -> boolean)') ,records)
    const envt2 = isOk(question_func_types) ? makeExtendTEnv(question_names,question_func_types.value,envt) : makeEmptyTEnv()
    
    const question_UD_names = map((rec_name) => `${rec_name}?`,names_UD)
    const question_UDfunc_types = mapResult((ud) => parseTE('(any -> boolean)') ,getTypeDefinitions(p))
    const envt3 = isOk(question_UDfunc_types) ? makeExtendTEnv(question_UD_names,question_UDfunc_types.value,envt2) : makeEmptyTEnv()

    
    const names_def = map((x : DefineExp) => x.var.var, getDefinitions(p))
    const define_texp = makeOk(map((x: DefineExp) => x.var.texp,getDefinitions(p)))
    const env_res = bind(define_texp, x => makeOk(makeExtendTEnv(names_def,x,envt3)))


    
    return isOk(env_res) ? env_res.value : makeEmptyTEnv()

    
}


export const fieldsTostringType = (record: Record): string => {
    const fields_types = map((x) => x.te, record.fields)
    const tmp_type = reduce((acc , field_type) => isNumTExp(field_type) ? acc + 'number * ' :
    isBoolTExp(field_type) ? acc + 'boolean * ' :
    isStrTExp(field_type) ? acc + 'string * ' :
    'a' ,'', fields_types)

    const type = slice(0,tmp_type.length - 3, tmp_type)
    return `(${type} -> ${record.typeName})`
} 
    


// Verify that user defined types and type-case expressions are semantically correct
// =================================================================================
// TODO L51
const checkUserDefinedTypes = (p: Program): Result<true> => {
    for(const rec of getRecords(p)) {
        const rec_parents = getRecordParents(rec.typeName,p)
        for(const ud of rec_parents) {
            for(const rec_of_ud of ud.records) {
                if(rec_of_ud.typeName === rec.typeName) {
                    if(rec_of_ud.fields.length !== rec.fields.length) {
                        return makeFailure('fields are not the same length')
                    }
                }
            }
        }
    }
    let b = true
    for(const ud of getTypeDefinitions(p)) {
        
        for(const rec of ud.records) {
            for(const field of rec.fields) {
                if(isUserDefinedNameTExp(field.te)) {
                    if(field.te.typeName === ud.typeName) {
                        b = ud.records.some((rec) => rec.fields.length === 0)
                        if(!b)
                            return makeFailure('not recursive supported')
                    }
                }
                
            }
            
        }
    }

    return makeOk(true)
}

// TODO L51
const checkTypeCase = (tc: TypeCaseExp, p: Program): Result<true> => {
    const ud_R = getUserDefinedTypeByName(tc.typeName,p)
    const records_string_R = bind(ud_R, (ud) => makeOk(map((x) => x.typeName ,ud.records)))
    const records_string = isOk(records_string_R) ? records_string_R.value : ''
    const case_strings = map(x => x.typeName,tc.cases)
    const ud = isOk(ud_R) ? ud_R.value : makeUserDefinedTExp('t',[])
    const ud_rec = ud.records
    const res : Result<boolean[]> = mapResult(ca => 
       records_string.includes(ca.typeName) ? bind(getRecordByName(ca.typeName,p), rec => makeOk(ca.varDecls.length === rec.fields.length)) : makeFailure('err') ,tc.cases)
    const pred = isOk(res) ? res.value : []
    const final_res = pred.every((x) => x=== true)

    
    return final_res ? makeOk(true) : makeFailure('case is not good')
} 
    


// Compute the type of L5 AST exps to TE
// ===============================================
// Compute a Typed-L5 AST exp to a Texp on the basis
// of its structure and the annotations it contains.

// Purpose: Compute the type of a concrete fully-typed expression
export const L51typeofProgram = (concreteExp: string): Result<string> =>
    bind(parseL51(concreteExp), (p: Program) =>
        bind(typeofExp(p, initTEnv(p), p), unparseTExp));

// For tests on a single expression - wrap the expression in a program
export const L51typeof = (concreteExp: string): Result<string> =>
    L51typeofProgram(`(L51 ${concreteExp})`);

// Purpose: Compute the type of an expression
// Traverse the AST and check the type according to the exp type.
// We assume that all variables and procedures have been explicitly typed in the program.
export const typeofExp = (exp: Parsed, tenv: TEnv, p: Program): Result<TExp> =>
    isNumExp(exp) ? makeOk(typeofNum(exp)) :
    isBoolExp(exp) ? makeOk(typeofBool(exp)) :
    isStrExp(exp) ? makeOk(typeofStr(exp)) :
    isPrimOp(exp) ? typeofPrim(exp) :
    isVarRef(exp) ? applyTEnv(tenv, exp.var) :
    isIfExp(exp) ? typeofIf(exp, tenv, p) :
    isProcExp(exp) ? typeofProc(exp, tenv, p) :
    isAppExp(exp) ? typeofApp(exp, tenv, p) :
    isLetExp(exp) ? typeofLet(exp, tenv, p) :
    isLetrecExp(exp) ? typeofLetrec(exp, tenv, p) :
    isDefineExp(exp) ? typeofDefine(exp, tenv, p) :
    isProgram(exp) ? typeofProgram(exp, tenv, p) :
    isSetExp(exp) ? typeofSet(exp, tenv, p) :
    isLitExp(exp) ? typeofLit(exp, tenv, p) :
    isDefineTypeExp(exp) ? typeofDefineType(exp, tenv, p) :
    isTypeCaseExp(exp) ? typeofTypeCase(exp, tenv, p) :
    makeFailure(`Unknown type: ${JSON.stringify(exp, null, 2)}`);

// Purpose: Compute the type of a sequence of expressions
// Check all the exps in a sequence - return type of last.
// Pre-conditions: exps is not empty.
export const typeofExps = (exps: Exp[], tenv: TEnv, p: Program): Result<TExp> => {
    return isEmpty(rest(exps)) ? typeofExp(first(exps), tenv, p) :
    bind(typeofExp(first(exps), tenv, p), _ => typeofExps(rest(exps), tenv, p));
}
    

// a number literal has type num-te
export const typeofNum = (n: NumExp): NumTExp => makeNumTExp();

// a boolean literal has type bool-te
export const typeofBool = (b: BoolExp): BoolTExp => makeBoolTExp();

// a string literal has type str-te
const typeofStr = (s: StrExp): StrTExp => makeStrTExp();

// primitive ops have known proc-te types
const numOpTExp = parseTE('(number * number -> number)');
const numCompTExp = parseTE('(number * number -> boolean)');
const boolOpTExp = parseTE('(boolean * boolean -> boolean)');

// L51 Todo: cons, car, cdr, list
export const typeofPrim = (p: PrimOp): Result<TExp> =>
    (p.op === '+') ? numOpTExp :
    (p.op === '-') ? numOpTExp :
    (p.op === '*') ? numOpTExp :
    (p.op === '/') ? numOpTExp :
    (p.op === 'and') ? boolOpTExp :
    (p.op === 'or') ? boolOpTExp :
    (p.op === '>') ? numCompTExp :
    (p.op === '<') ? numCompTExp :
    (p.op === '=') ? numCompTExp :
    // Important to use a different signature for each op with a TVar to avoid capture
    (p.op === 'number?') ? parseTE('(T -> boolean)') :
    (p.op === 'boolean?') ? parseTE('(T -> boolean)') :
    (p.op === 'string?') ? parseTE('(T -> boolean)') :
    (p.op === 'list?') ? parseTE('(T -> boolean)') :
    (p.op === 'pair?') ? parseTE('(T -> boolean)') :
    (p.op === 'symbol?') ? parseTE('(T -> boolean)') :
    (p.op === 'not') ? parseTE('(boolean -> boolean)') :
    (p.op === 'eq?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'string=?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'display') ? parseTE('(T -> void)') :
    (p.op === 'newline') ? parseTE('(Empty -> void)') :
    makeFailure(`Primitive not yet implemented: ${p.op}`);

// TODO L51
// Change this definition to account for possibility of subtype expressions between thenTE and altTE
// 
// Purpose: compute the type of an if-exp
// Typing rule:
//   if type<test>(tenv) = boolean
//      type<then>(tenv) = t1
//      type<else>(tenv) = t1
// then type<(if test then else)>(tenv) = t1
export const typeofIf = (ifExp: IfExp, tenv: TEnv, p: Program): Result<TExp> => {
    const testTE = typeofExp(ifExp.test, tenv, p);
    const thenTE = typeofExp(ifExp.then, tenv, p);
    const altTE = typeofExp(ifExp.alt, tenv, p);
    const constraint1 = bind(testTE, testTE => checkEqualType(testTE, makeBoolTExp(), ifExp, p));
    const constraint2 = bind(thenTE, (thenTE: TExp) =>
                            bind(altTE, (altTE: TExp) =>
                                checkCoverType([thenTE,altTE],p)));                            
    return bind(constraint1, () =>  constraint2);
};

// Purpose: compute the type of a proc-exp
// Typing rule:
// If   type<body>(extend-tenv(x1=t1,...,xn=tn; tenv)) = t
// then type<lambda (x1:t1,...,xn:tn) : t exp)>(tenv) = (t1 * ... * tn -> t)
export const typeofProc = (proc: ProcExp, tenv: TEnv, p: Program): Result<TExp> => {
    const argsTEs = map((vd) => vd.texp, proc.args);
    const extTEnv = makeExtendTEnv(map((vd) => vd.var, proc.args), argsTEs, tenv);
    const constraint1 = bind(typeofExps(proc.body, extTEnv, p), (body: TExp) => 
                            checkEqualType(body, proc.returnTE, proc, p));
    return bind(constraint1, (returnTE: TExp) => makeOk(makeProcTExp(argsTEs, returnTE)));
};

// Purpose: compute the type of an app-exp
// Typing rule:
// If   type<rator>(tenv) = (t1*..*tn -> t)
//      type<rand1>(tenv) = t1
//      ...
//      type<randn>(tenv) = tn
// then type<(rator rand1...randn)>(tenv) = t
// We also check the correct number of arguments is passed.
export const typeofApp = (app: AppExp, tenv: TEnv, p: Program): Result<TExp> =>
    bind(typeofExp(app.rator, tenv, p), (ratorTE: TExp) => {
        // console.log(app)
        if (! isProcTExp(ratorTE)) {
            return bind(unparseTExp(ratorTE), (rator: string) =>
                        bind(unparse(app), (exp: string) =>
                            makeFailure<TExp>(`Application of non-procedure: ${rator} in ${exp}`)));
        }
        if (app.rands.length !== ratorTE.paramTEs.length) {
            return bind(unparse(app), (exp: string) => makeFailure<TExp>(`Wrong parameter numbers passed to proc: ${exp}`));
        }
        const constraints = zipWithResult((rand, trand) => bind(typeofExp(rand, tenv, p), (typeOfRand: TExp) =>  
                                                                checkEqualType(typeOfRand, trand, app, p)),
                                          app.rands, ratorTE.paramTEs);
                                          
        
        // console.log(app.rator)
        // console.log(ratorTE.paramTEs)
        return mapv(constraints, _ => ratorTE.returnTE);
    });

// Purpose: compute the type of a let-exp
// Typing rule:
// If   type<val1>(tenv) = t1
//      ...
//      type<valn>(tenv) = tn
//      type<body>(extend-tenv(var1=t1,..,varn=tn; tenv)) = t
// then type<let ((var1 val1) .. (varn valn)) body>(tenv) = t
export const typeofLet = (exp: LetExp, tenv: TEnv, p: Program): Result<TExp> => {
    const vars = map((b) => b.var.var, exp.bindings);
    const vals = map((b) => b.val, exp.bindings);
    const varTEs = map((b) => b.var.texp, exp.bindings);
    const constraints = zipWithResult((varTE, val) => bind(typeofExp(val, tenv, p), (typeOfVal: TExp) => 
                                                            checkEqualType(varTE, typeOfVal, exp, p)),
                                      varTEs, vals);
    return bind(constraints, _ => typeofExps(exp.body, makeExtendTEnv(vars, varTEs, tenv), p));
};

// Purpose: compute the type of a letrec-exp
// We make the same assumption as in L4 that letrec only binds proc values.
// Typing rule:
//   (letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)
//   tenv-body = extend-tenv(p1=(t11*..*t1n1->t1)....; tenv)
//   tenvi = extend-tenv(xi1=ti1,..,xini=tini; tenv-body)
// If   type<body1>(tenv1) = t1
//      ...
//      type<bodyn>(tenvn) = tn
//      type<body>(tenv-body) = t
// then type<(letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)>(tenv-body) = t
export const typeofLetrec = (exp: LetrecExp, tenv: TEnv, p: Program): Result<TExp> => {
    const ps = map((b) => b.var.var, exp.bindings);
    const procs = map((b) => b.val, exp.bindings);
    if (! allT(isProcExp, procs))
        return makeFailure(`letrec - only support binding of procedures - ${JSON.stringify(exp, null, 2)}`);
    const paramss = map((p) => p.args, procs);
    const bodies = map((p) => p.body, procs);
    const tijs = map((params) => map((p) => p.texp, params), paramss);
    const tis = map((proc) => proc.returnTE, procs);
    const tenvBody = makeExtendTEnv(ps, zipWith((tij, ti) => makeProcTExp(tij, ti), tijs, tis), tenv);
    const tenvIs = zipWith((params, tij) => makeExtendTEnv(map((p) => p.var, params), tij, tenvBody),
                           paramss, tijs);
    const types = zipWithResult((bodyI, tenvI) => typeofExps(bodyI, tenvI, p), bodies, tenvIs)
    const constraints = bind(types, (types: TExp[]) => 
                            zipWithResult((typeI, ti) => checkEqualType(typeI, ti, exp, p), types, tis));
    return bind(constraints, _ => typeofExps(exp.body, tenvBody, p));
};

// TODO - write the true definition
// Purpose: compute the type of a define
// Typing rule:
//   (define (var : texp) val)
//   tenv-val = extend-tenv(var:texp; tenv)
// If   type<val>(tenv-val) = texp
// then type<(define (var : texp) val)>(tenv) = void
export const typeofDefine = (exp: DefineExp, tenv: TEnv, p: Program): Result<VoidTExp> => {
    const v = exp.var.var;
    const texp = exp.var.texp;
    const val = exp.val;
    const tenvVal = makeExtendTEnv([v], [texp], tenv);
    const constraint = typeofExp(val, tenvVal, p);
    return mapv(constraint, (_) => makeVoidTExp());
};

// Purpose: compute the type of a program
// Typing rule:
export const typeofProgram = (exp: Program, tenv: TEnv, p: Program): Result<TExp> =>
    typeofExps(exp.exps, tenv, p);

// TODO L51
// Write the typing rule for DefineType expressions
export const typeofDefineType = (exp: DefineTypeExp, _tenv: TEnv, _p: Program): Result<TExp> => {
    return bind(checkUserDefinedTypes(_p), () => makeOk(makeVoidTExp()))
}
    


// TODO L51
export const typeofSet = (exp: SetExp, _tenv: TEnv, _p: Program): Result<TExp> => {
    const constraints = bind(typeofExp(exp.val, _tenv, _p), (valte) => 
    bind(applyTEnv(_tenv, exp.var.var), (varte) =>
    checkEqualType(valte,varte,exp,_p)));
    
    return bind(constraints, () => makeOk(makeVoidTExp()));
}
    

// TODO L51
export const typeofLit = (exp: LitExp, _tenv: TEnv, _p: Program): Result<TExp> =>
    isNumExp(exp.val) ? makeOk(makeNumTExp()) :
    exp.val === true ? makeOk(makeBoolTExp()) :
    exp.val === false ? makeOk(makeBoolTExp()) :
    isStrExp(exp.val) ? makeOk(makeStrTExp()) :
    makeFailure("not a lit")
    

// TODO: L51
// Purpose: compute the type of a type-case
// Typing rule:
// For all user-defined-type id
//         with component records record_1 ... record_n
//         with fields (field_ij) (i in [1...n], j in [1..R_i])
//         val CExp
//         body_i for i in [1..n] sequences of CExp
//   ( type-case id val (record_1 (field_11 ... field_1r1) body_1)...  )
//  TODO
export const typeofTypeCase = (exp: TypeCaseExp, tenv: TEnv, p: Program): Result<TExp> => {
    
    const type_of_case = getUserDefinedTypeByName(exp.typeName,p)
    const case_type_te = applyTEnv(tenv,(exp.val as VarRef).var)
    

    

    const cases_parents = mapResult((rec) => bind(type_of_case, udt => makeOk(getRecordParents(rec.typeName,p).includes(udt))), exp.cases)
    const constrain1 = bind(checkTypeCase(exp,p), () => bind(cases_parents, (res) => makeOk(res.every(b => b === true))))

    const is_record : Result<Record> = getRecordByName(exp.typeName,p)



    if(isOk(is_record)) {
        const ud : Result<UserDefinedTExp> = (bind(is_record, (rec : Record) => makeOk(getTypeDefinitions(p).find((ud) => ud.records.includes(rec)))) as Result<UserDefinedTExp>)
        
        return bind(ud , (udt) => makeOk(makeUserDefinedNameTExp(udt.typeName)))
        
    }

    const choosen_case : Result<CaseExp> = bind(case_type_te,(cte) => isUserDefinedNameTExp(cte) ? makeOk(filter((ce) => ce.typeName === cte.typeName ,exp.cases)[0]) : makeFailure('err') )
    
    

    if(isOk(choosen_case)){
        if(choosen_case.value !== undefined){
            const recfields = bind(getRecordByName(choosen_case.value.typeName,p), rec => makeOk(map((field) => field.te ,rec.fields)))
            const extTEnv = bind(recfields, (argsTEs_v) => bind(choosen_case,(ce) =>  makeOk(makeExtendTEnv(map((vd) => vd.var, ce.varDecls), argsTEs_v, tenv))))
            const ct = bind(extTEnv, (extTEnv_v) => bind(choosen_case, (ce) => typeofExps(ce.body, extTEnv_v, p)))
            
            
                                        
            return bind(constrain1, (x) => x ? ct : makeFailure('err'))
        }
        else{
            return bind(case_type_te, (ce) => makeOk(ce))
        }
    }
    else{
        return makeFailure('error')
    }
   
}