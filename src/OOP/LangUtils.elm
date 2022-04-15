module OOP.LangUtils exposing (..)

import List exposing (length)
import OOP.Syntax exposing (..)
import OOP.Utils exposing (findByName)
import OOP.Printer.Value exposing (printValue)

processAfterParse : Term -> Term
processAfterParse term =
    case term of
        TLam ws p t ->
            let
                t_ =
                    processAfterParse t
            in
                TLam ws p t_
        
        TApp ws t1 t2 ->
            let
                t1_ =
                    processAfterParse t1
                
                t2_ =
                    processAfterParse t2
            in
                TApp ws t1_ t2_

        TLet ws p t1 t2 ->
            let
                t1_ =
                    processAfterParse t1
                
                t2_ =
                    processAfterParse t2
            in
                TLet ws p t1_ t2_

        TLetrec ws p t1 t2 ->
            let
                t1_ =
                    processAfterParse t1
                
                t2_ =
                    processAfterParse t2
            in
                TLetrec ws p t1_ t2_

        TFix ws t ->
            let
                t_ =
                    processAfterParse t
            in
                TFix ws t_
            
        TCase ws guard br ->
            let
                (br_, _) =
                    addIDToBranch br 0
            in
                TCase ws guard br_

        TCons ws t1 t2 ->
            let
                t1_ =
                    processAfterParse t1
                
                t2_ =
                    processAfterParse t2
            in
                TCons ws t1_ t2_

        TList ws t1 t2 ->
            let
                t1_ =
                    processAfterParse t1
                
                t2_ =
                    processAfterParse t2
            in
                TList ws t1_ t2_

        TTuple2 ws t1 t2 ->
            let
                t1_ =
                    processAfterParse t1
                
                t2_ =
                    processAfterParse t2
            in
                TTuple2 ws t1_ t2_
        
        TTuple3 ws t1 t2 t3 ->
            let
                t1_ =
                    processAfterParse t1
                
                t2_ =
                    processAfterParse t2

                t3_ =
                    processAfterParse t3
            in
                TTuple3 ws t1_ t2_ t3_

        TBPrim ws op t1 t2 ->
            let
                t1_ =
                    processAfterParse t1
                
                t2_ =
                    processAfterParse t2
            in
                TBPrim ws op t1_ t2_

        TUPrim ws op t ->
            let
                t_ =
                    processAfterParse t
            in
                TUPrim ws op t_

        TParens ws t ->
            let
                t_ =
                    processAfterParse t
            in
                TParens ws t_

        TRef ws t ->
            let
                t_ =
                    processAfterParse t
            in
                TRef ws t_

        TDeRef ws t ->
            let
                t_ =
                    processAfterParse t
            in
                TDeRef ws t_

        TAssign ws t1 t2 ->
            let
                t1_ =
                    processAfterParse t1
                
                t2_ =
                    processAfterParse t2
            in
                TAssign ws t1_ t2_

        TField ws t f ->
            let
                t_ =
                    processAfterParse t
            in
                TField ws t_ f

        TInvk ws t m ->
            let
                t_ =
                    processAfterParse t
            in
                TInvk ws t_ m

        TNew ws c t ->
            let
                t_ =
                    processAfterParse t
            in
                TNew ws c t_
        
        _ -> term


addIDToBranch : Branch -> ID -> (Branch, ID)
addIDToBranch br id =
    case br of
        BSin ws p t ->
            let
                t_ =
                    processAfterParse t
            in
            (BNSin ws id p t_, id+1)
        
        BCom ws b1 b2 ->
            let
                (b1_, id1) =
                    addIDToBranch b1 id
                
                (b2_, id2) =
                    addIDToBranch b2 id1
            in
                (BCom ws b1_ b2_, id2)
        
        _ -> (br, id)


match : Pattern -> Value -> Env
match pat val =
    case (pat, val) of

        ((PString _ p1 p2), (VString v1 v2)) ->
            matchHelper p1 p2 v1 v2

        ((PCons _ p1 p2), (VCons v1 v2)) ->
            matchHelper p1 p2 v1 v2

        ((PList _ p1 p2), (VCons v1 v2)) ->
            matchHelper p1 p2 v1 v2

        ((PBTuple _ p1 p2), (VTuple2 v1 v2)) ->
            matchHelper p1 p2 v1 v2
        
        ((PTTuple _ p1 p2 p3), (VTuple3 v1 v2 v3)) ->
            let
                res1 = 
                    match p1 v1

                res2 =
                    match p2 v2

                res3 =
                    match p3 v3
            in
            if res1 == [("ERROR", VError "Match Failed.")] ||
                res2 == [("ERROR", VError "Match Failed.")] ||
                res3 == [("ERROR", VError "Match Failed.")]
            then 
                [("ERROR", VError "Match Failed.")]
            else
                res1++res2++res3

        ((PInt _ n1), (VInt n2)) ->
            if n1 == n2 then [] else [("ERROR", VError "Match Failed.")]

        ((PFloat _ n1), (VFloat n2)) ->
            if n1 == n2 then [] else [("ERROR", VError "Match Failed.")]

        (PTrue _,  VTrue)     -> []
        (PFalse _, VFalse)    -> []

        (PChar _ c1, VChar c2) ->
            if c1 == c2 then [] else [("ERROR", VError "Match Failed.")]
        
        (PNil _, VNil)       -> []
        (PEmpList _, VNil)   -> []
        (PEmpStr _, VEmpStr) -> []

        (PVar _ s, v) -> [(s, v)]

        _ -> [("ERROR", VError "Match Failed.")]


matchHelper : Pattern -> Pattern -> Value -> Value -> Env
matchHelper p1 p2 v1 v2 =
    let
        res1 = 
            match p1 v1

        res2 =
            match p2 v2
    in
    if res1 == [("ERROR", VError "Match Failed.")] ||
        res2 == [("ERROR", VError "Match Failed.")]
    then 
        [("ERROR", VError "Match Failed.")]
    else
        res1++res2


matchCase : Value -> Branch -> MatchCaseRes
matchCase v b =
    case b of
        BNSin _ n p t ->
            { envm  = match p v
            , choice = n
            , ti = t
            , pi = p
            }

        BCom _ b1 b2 ->
            let 
                res = 
                    matchCase v b1 
            in
                case res.envm of
                    [(_, VError _)] ->
                        matchCase v b2
                    
                    _ -> res
        
        _ ->
            { envm  = []
            , choice = 0
            , ti = TError "Match Case Error : 01."
            , pi = PError
            }


-- Ignore spaces here for convenience
findClass : String -> ClassTable -> Maybe ClassDef
findClass class classtb =
    let
        (_, classtb_)=
            classtb
    in
        case classtb_ of
            (_,((c,f),fs,ms)) :: cds ->
                if c == class
                then 
                    Just ([], ((c,f),fs,ms))
                else
                    findClass class ([], cds)
                    
            _ -> Nothing


getFields : String -> ClassTable -> List (WS, String, String)
getFields class classtb =
    let
        res = 
            findClass class classtb
    in
        case res of
            Just (_, ((_,f),(_, fs),_)) ->
                if f == "Object"
                then
                    fs
                else
                    (getFields f classtb) ++ fs
            Nothing ->
                []


findIndexValueList : Int -> Value -> Maybe Value
findIndexValueList id val =
    case val of
        VCons v vs ->
            if id == 0
            then
                Just v
            else
                findIndexValueList (id - 1) vs
        VNil ->
            Nothing

        _ ->
            Just (VError "Args is Not a List : 01.")


findIndexMethods : String -> Methods -> Maybe Method
findIndexMethods m methods =
    let
        (_, ms) = methods
    in
    case ms of
        (_, (m_, p, t)) :: ms_ ->
            if m == m_
            then
                Just ([], (m, p, t))
            else
                findIndexMethods m ([], ms_)

        [] ->
            Nothing


findMethod : String -> String -> ClassTable -> Maybe (String, Method)
findMethod m c classtb =
    let
        res =
            findClass c classtb
    in
        case res of
            Just (_, ((_, f),_,ms)) ->
                if f == "Object"
                then
                    Maybe.map (\a -> (c, a)) (findIndexMethods m ms)
                else
                    case (findIndexMethods m ms) of
                        Just mthd ->
                            Just (c, mthd)

                        Nothing ->
                            findMethod m f classtb
            _ -> Nothing


valueToTerm : Value -> WS -> Term
valueToTerm v ws =
    case v of
        VInt n -> TInt ws n

        VFloat n -> TFloat ws n

        VTrue -> TTrue ws

        VFalse -> TFalse ws

        VChar c -> TChar ws c

        VString v1 v2 ->
            let
                t1 =
                    valueToTerm v1 [""]

                t2 =
                    valueToTerm v2 [""]
            in
                TString ws t1 t2

        VEmpStr -> TEmpStr ws

        VCons v1 v2 ->
            case ws of
                [_] ->
                    let
                        t1 =
                            valueToTerm v1 [""]

                        t2 =
                            valueToTerm v2 [" "]
                    in
                        TCons ws t1 t2

                [_, _] ->
                    valueToListTerm v ws

                _ ->
                    TError "Error : 34."

        VNil -> TNil ws

        VTuple2 v1 v2 ->
            let
                t1 =
                    valueToTerm v1 [""]

                t2 =
                    valueToTerm v2 [""]
            in
                TTuple2 ws t1 t2

        VTuple3 v1 v2 v3 ->
            let
                t1 =
                    valueToTerm v1 [""]

                t2 =
                    valueToTerm v2 [""]
                
                t3 =
                    valueToTerm v3 [""]
            in
                TTuple3 ws t1 t2 t3

        VLoc n -> TLoc ws n

        VUnit -> TUnit ws

        VNew class arg ->
            let
                t =
                    valueToTerm arg ["",""]
            in
                TNew [" ", "", ""] class t

        _ ->
            TError ("Can Not Transfer Value: "++(printValue v)++" To Expression.")

    
valueToListTerm : Value -> WS -> Term
valueToListTerm v ws =
    case v of
        VCons v1 v2 ->
            let
                t1 =
                    valueToTerm v1 [""]
                
                t2 =
                    valueToListTerm v2 [" "]
            in
                TList ws t1 t2

        VNil ->
            TEmpList []

        _ ->
            TError "Error : 33."


patternSubst : Env -> Pattern -> Value
patternSubst env p = 
    case p of
        PVar _ s ->
            case findByName s env of
                Just val ->
                    val
                
                Nothing  ->
                    VError "Pattern Substitution Error: No Such Variable."
        
        PCons _ p1 p2 ->
                VCons (patternSubst env p1) (patternSubst env p2)

        PNil _ -> VNil

        PList _ p1 p2 ->
                VCons (patternSubst env p1) (patternSubst env p2)
            
        PEmpList _ -> VNil

        PInt _ n     -> VInt n

        PFloat _ n   -> VFloat n

        PTrue _     -> VTrue

        PFalse _     -> VFalse

        PString _ p1 p2 ->
                VString (patternSubst env p1) (patternSubst env p2)

        PEmpStr _ -> VEmpStr

        PChar _ c -> VChar c

        PBTuple _ p1 p2 ->
            VTuple2 (patternSubst env p1) (patternSubst env p2)

        PTTuple _ p1 p2 p3 ->
            VTuple3 (patternSubst env p1) 
                    (patternSubst env p2)
                    (patternSubst env p3)
    
        PUnit _ -> VUnit

        PError -> VError "Error : 07."


mergeEnv : Env -> Env -> Env -> Env
mergeEnv env1 env2 ori_env =

    case (env1, env2, ori_env) of

        ((s1, v1)::env1_, (s2, v2)::env2_, (_, v3)::ori_env_) ->
            case (v1, v3) of
                (VClosure _ t1 _, VFix (TLam _ _ (TLam _ _ t2))) ->
                    if (t1 /= t2) 
                    then (s1, v1) :: mergeEnv env1_ env2_ ori_env_
                    else (s2, v2) :: mergeEnv env1_ env2_ ori_env_

                _ ->
                    if (v1 /= v3) 
                    then (s1, v1) :: mergeEnv env1_ env2_ ori_env_
                    else (s2, v2) :: mergeEnv env1_ env2_ ori_env_
        
        _ ->
            []


mergeClassTable : ClassTable -> ClassTable -> ClassTable -> ClassTable -> ClassTable
mergeClassTable classtb1 classtb2 classtb3 classtbo =
    let
        (_, ct1) = classtb1

        (_, ct2) = classtb2

        (_, ct3) = classtb3

        (ws_tb, cto) = classtbo
    in
    case (ct1, ct2, (ct3, cto)) of

        ((_, ((c,f),fields,ls1))::ct1_, (_, (_,_,ls2))::ct2_, ((_, (_,_,ls3))::ct3_,(ws_cd, (_,_,lso))::cto_)) ->
            let
                res =
                    Tuple.second <| mergeClassTable ([],ct1_) ([],ct2_) ([],ct3_) ([],cto_)
            in
            (ws_tb, (ws_cd, ((c,f),fields,(mergeMethods ls1 ls2 ls3 lso))) :: res)

        _ -> ([], [])


mergeMethods : Methods -> Methods -> Methods -> Methods -> Methods
mergeMethods methods1 methods2 methods3 methodso =
    let
        (_, ls1) = methods1

        (_, ls2) = methods2

        (_, ls3) = methods3

        (ws_ms, lso) = methodso
    in
    case (ls1, ls2, (ls3, lso)) of

        ((_, (s,p,t1))::ls1_, (_, (_,_,t2))::ls2_, ((_, (_,_,t3))::ls3_, (ws_m, (_,_,to))::lso_)) ->
            let
                res =
                    Tuple.second <| mergeMethods ([],ls1_) ([],ls2_) ([],ls3_) ([],lso_)
            in
            if (t1 /= to) then 
                (ws_ms, (ws_m,(s,p,t1)) :: res)
            else if (t2 /= to) then
                (ws_ms, (ws_m,(s,p,t2)) :: res)
            else
                (ws_ms, (ws_m,(s,p,t3)) :: res)

        _ -> ([],[])


updateBranch : Branch -> Int -> Term -> Branch
updateBranch branch choice t =
    case branch of
        BNSin ws n p term ->
            if choice == n
            then BNSin ws n p t
            else BNSin ws n p term

        BCom ws b1 b2 ->
            BCom ws (updateBranch b1 choice t) (updateBranch b2 choice t)
        
        b -> b


vlength : Value -> Int
vlength v =
    case v of
        VNil ->
            0

        VCons _ vs ->
            1 + (vlength vs)

        VEmpStr ->
            0

        VString _ vs ->
            1 + (vlength vs)
        
        _ ->
            -99


vtake : Value -> Int -> Value
vtake v n =
    case v of
        VNil ->
            VNil
        
        VCons v1 vs ->
            if n == 0 then
                VNil
            else
                VCons v1 (vtake vs (n - 1))
        
        VEmpStr ->
            VEmpStr

        VString v1 vs ->
            if n == 0 then
                VEmpStr
            else
                VString v1 (vtake vs (n - 1))

        _ ->
            VError "The Take function cannot be used on values other than lists and strings."


vsplit : Value -> Int -> (Value, Value)
vsplit nl n1 =
    case (nl, n1) of
        (VCons _ _, 0) ->
            (VNil, nl)
        
        (VCons v1 vs, _) ->
            let
                (l1, l2) =
                    vsplit vs (n1 - 1)
            in
                (VCons v1 l1, l2)

        (VNil, _) ->
            (VNil, VNil)

        (VString _ _, 0) ->
            (VEmpStr, nl)
        
        (VString v1 vs, _) ->
            let
                (l1, l2) =
                    vsplit vs (n1 - 1)
            in
                (VString v1 l1, l2)

        (VEmpStr, _) ->
            (VEmpStr, VEmpStr)
        
        _ ->
            ( VError "New Value for Updating Concat Type Error"
            , VError "")


vreplace : Int -> Value -> Value -> Value
vreplace index v ls =
    case ls of
        VNil ->
            VNil

        VCons v1 v2 ->
            if index == 0 then
                VCons v v2
            else
                VCons v1 (vreplace (index - 1) v v2)

        _ ->
            VError "Args is Not a List : 02."


updateClassTable : String -> String -> Term -> ClassTable -> ClassTable
updateClassTable m class t_ classtb =
    let
        res =
            findMethod m class classtb
    in
        case res of
            Just (owner, _) ->
                replaceClassMethods owner m t_ classtb

            Nothing ->
                classtb


replaceClassMethods : String -> String -> Term -> ClassTable -> ClassTable
replaceClassMethods class m t_ classtable =
    let
        (ws_tb, classtb) = classtable
    in
    case classtb of
        (ws_cd, ((c,f),fs,ms)) :: cds ->
            if c == class
            then 
                (ws_tb, (ws_cd, ((c,f),fs,replaceMethods m t_ ms)) :: cds)
            else
                (ws_tb, (ws_cd, ((c,f),fs,ms)) :: (Tuple.second <| replaceClassMethods class m t_ ([], cds)))

        [] -> ([], [])


replaceMethods : String -> Term -> Methods -> Methods
replaceMethods m t_ methods =
    let
        (ws_ms, ms) = methods
    in
    case ms of
        (ws_m, (m_, p, t)) :: ms_ ->
            if m == m_
            then
                (ws_ms, (ws_m, (m_, p, t_)) :: ms_)
            else
                (ws_ms, (ws_m, (m_, p, t)) :: (Tuple.second <| replaceMethods m t_ ([], ms_)))

        [] ->
            ([], [])


findFieldsIndex : String -> List (Int, (WS, String, String)) -> Int
findFieldsIndex s env =
    case env of

        (n, (_, x, _)) :: env_ ->
            if s == x then n else findFieldsIndex s env_

        [] -> -1


strToVString : List Char -> Value
strToVString lc =
    case lc of
        [] ->
            VEmpStr

        c :: cs ->
            VString (VChar c) (strToVString cs)


appendTermString : Term -> Term -> Term
appendTermString l1 l2 =
    case l1 of
        TEmpStr _ -> l2

        TString ws v1 vs1 ->
            TString ws v1 (appendTermString vs1 l2 )
        
        _ ->
            TError "Operand Error : 14."


strToTString : List Char -> Term
strToTString lc =
    case lc of
        [] ->
            TEmpStr []

        c :: cs ->
            TString [] (TChar [] c) (strToTString cs)


appendValueList : Value -> Value -> Value
appendValueList l1 l2 =
    case l1 of
        VNil -> l2

        VCons v1 vs1 ->
            VCons v1 (appendValueList vs1 l2)

        _ ->
            VError "Operand Error : 06."


appendValueString : Value -> Value -> Value
appendValueString l1 l2 =
    case l1 of
        VEmpStr -> l2

        VString v1 vs1 ->
            VString v1 (appendValueString vs1 l2 )
        
        _ ->
            VError "Operand Error : 11."


printEnv : Env -> String
printEnv env =
    case env of
        (s, v) :: env_ ->
            if (printValue v) == "<fn>" || (printValue v) == "<fix>" then
                (printEnv env_)
            else
                s ++ ": " ++ (printValue v) ++ ";   " ++ (printEnv env_)
        
        [] ->
            "\n"


printState : State -> String
printState state =
    case state of
        v :: rest ->
            (printValue v) ++ ",  " ++ (printState rest)
        
        [] ->
            ""


diff : Value -> Value -> (Int, List DiffOp)
diff v1 v2 =
    case v1 of
        VNil -> 
            (vlength v2, turnToInsert v2)
    
        VEmpStr ->
            (vlength v2, turnToInsert v2)

        VCons v11 v12 ->
            case v2 of
                VNil ->
                    (vlength v1, List.repeat (vlength v1) Delete)

                VCons v21 v22 ->
                    if v11 == v21 then
                        let
                            (n, opList) =
                                diff v12 v22
                        in
                            (n, Keep :: opList)
                    else
                        compareSubSeq v21 (diff v12 v22) (diff v1 v22) (diff v12 v2)

                _ ->
                    (-99, [])

        VString v11 v12 ->
            case v2 of
                VEmpStr ->
                    (vlength v1, List.repeat (vlength v1) Delete)

                VString v21 v22 ->
                    if v11 == v21 then
                        let
                            (n, opList) =
                                diff v12 v22
                        in
                            (n, Keep :: opList)
                    else
                        compareSubSeq v21 (diff v12 v22) (diff v1 v22) (diff v12 v2)

                _ ->
                    (-99, [])

        _ ->
            (0, [])


turnToInsert : Value -> List DiffOp
turnToInsert v =
    case v of
        VNil -> 
            []

        VCons v1 v2 ->
            (Insert v1) :: turnToInsert v2
        
        VEmpStr -> 
            []

        VString v1 v2 ->
            (Insert v1) :: turnToInsert v2

        _ ->
            []


compareSubSeq : Value -> (Int, List DiffOp) -> (Int, List DiffOp) -> (Int, List DiffOp) -> (Int, List DiffOp)
compareSubSeq v (n1, ls1) (n2, ls2) (n3, ls3) =
    if n1 <= n2 && n1 <= n3 then
        (n1 + 1, (Update v) :: ls1)
    else if n2 <= n3 then
        (n2 + 1, (Insert v) :: ls2)
    else
        (n3 + 1, Delete :: ls3)


mergeState : State -> State -> State -> Result String State
mergeState state1 state2 state =
    if length state1 /= length state || length state2 /= length state then
        Result.Err "Merge State Error : 01."
    else
        case (state1, state2, state) of
            (v1::st1, v2::st2, v::st) ->
                if v1 /= v then
                    Result.map (\res -> v1::res ) (mergeState st1 st2 st)
                else
                    Result.map (\res -> v2::res ) (mergeState st1 st2 st)

            ([], [], []) ->
                Result.Ok []

            _ ->
                Result.Err "Merge State Error : 02."


splitFuncDef : List Pattern -> Term -> (List Pattern, Term)
splitFuncDef params t =
    case t of
        TLam [] p t_ ->
            splitFuncDef (p :: params) t_

        _ -> (List.reverse params, t)