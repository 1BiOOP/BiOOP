module OOP.Eval exposing (..)

import OOP.Syntax exposing(..)
import OOP.Utils exposing (..)
import OOP.LangUtils exposing (..)
import Utils exposing (nth)
import OOP.Printer.Value exposing (printValue)
import Round
import List
import Tuple

eval : Env -> State -> ClassTable -> Term -> (Value, State)
eval env state classtb term =
    case term of

        TInt _ n -> (VInt n, state)

        TFloat _ n -> (VFloat n, state)

        TTrue _ -> (VTrue, state)

        TFalse _ -> (VFalse, state)

        TChar _ c -> (VChar c, state)

        TString _ t1 t2 -> 
            let
                (v1, state1) =
                    eval env state classtb t1

                (v2, state2) =
                    eval env state1 classtb t2
            in
                (VString v1 v2, state2)

        TEmpStr _ -> (VEmpStr, state)

        TVar _ s ->
            case findByName s env of
                Nothing -> (VError "No Such Variable : 01", [])

                Just v -> 
                    case v of
                        -- TODO: FIX
                        VFix t -> eval env state classtb (TFix [] t)
                        _ -> (v, state)

        TLam _ p t -> (VClosure p t env, state)

        TApp _ t1 t2 ->
            case eval env state classtb t1 of

                (VClosure p tf envf, state1) ->
                    case t2 of
                        TFix _ t -> 
                            case p of
                                PVar _ s -> eval ((s, VFix t)::envf) state1 classtb  tf 
                                _      -> (VError "Recursion Error : 01.", [])
                        _ ->  
                            let 
                                (v2, state2) =
                                    eval env state1 classtb t2
                                
                                envm =
                                    match p v2
                            in
                            case envm of
                                [(_, VError info)] -> (VError info, [])
                                _             -> eval (envm++envf) state2 classtb tf

                _ -> (VError "Not Applicable : 01.", [])

        TLet _ p t1 t2 ->
            eval env state classtb (TApp [] (TLam [] p t2) t1)

        TLetrec _ p t1 t2 ->
            eval env state classtb 
                (TApp [] (TLam [] p t2) (TFix [] (TLam [] p t1)))

        TFix _ t ->
            eval env state classtb (TApp [] t (TFix [] t))

        TCase _ (TVar _ s) branch ->
            case findByName s env of
                Just v ->
                    let
                        res = 
                            matchCase v branch 
                    in
                    case res.envm of
                        [(_, VError info)] -> (VError info, [])
                        _ -> eval (res.envm++env) state classtb res.ti
                
                Nothing ->
                    (VError "No Such Variable : 02", [])
        
        TCons _ t1 t2 ->
            let 
                (v1, state1) =
                    eval env state classtb t1

                (v2, state2) =
                    eval env state1 classtb t2
            in
                (VCons v1 v2, state2)

        TList _ t1 t2 ->
            let 
                (v1, state1) =
                    eval env state classtb t1

                (v2, state2) =
                    eval env state1 classtb t2
            in
                (VCons v1 v2, state2)

        TNil _ -> (VNil, state)

        TEmpList _ -> (VNil, state)

        TTuple2 _ t1 t2 ->
            let 
                (v1, state1) =
                    eval env state classtb t1

                (v2, state2) =
                    eval env state1 classtb t2
            in
                (VTuple2 v1 v2, state2)

        TTuple3 _ t1 t2 t3 ->
            let 
                (v1, state1) =
                    eval env state classtb t1

                (v2, state2) =
                    eval env state1 classtb t2

                (v3, state3) =
                    eval env state2 classtb t3
            in
                (VTuple3 v1 v2 v3, state3)

        TBPrim _ op t1 t2 ->
            let 
                (v1, state1) = 
                    eval env state classtb t1 

                (v2, state2) = 
                    eval env state1 classtb t2
            in
                case v1 of
                    VInt n1 ->
                        case v2 of
                            VInt n2 -> 
                                (intOp op n1 n2, state2)
                            
                            VFloat n2 ->
                                (floatOp op (toFloat n1) n2, state2)
                            
                            _ -> (VError "Operand Error : 01.", [])

                    VFloat n1 ->
                        case v2 of
                            VInt n2   -> 
                                (floatOp op n1 (toFloat n2), state2)

                            VFloat n2 -> 
                                (floatOp op n1 n2, state2)
                            
                            _         -> (VError "Operand Error : 02.", [])

                    VTrue ->
                        case v2 of
                            VTrue ->
                                case op of
                                And -> (VTrue, state2)
                                Or  -> (VTrue, state2)
                                _   -> (VError "Operator Error : 03.", [])
                            
                            VFalse ->
                                case op of
                                    And -> (VFalse, state2)
                                    Or  -> (VTrue, state2)
                                    _   -> (VError "Operator Error: 04.", [])

                            _ -> (VError "Operand Error : 03.", [])

                    VFalse ->
                        case v2 of
                            VTrue ->
                                case op of
                                    And -> (VFalse, state2)
                                    Or  -> (VTrue, state2)
                                    _   -> (VError "Operator Error : 05.", [])
                            
                            VFalse ->
                                case op of
                                    And -> (VFalse, state2)
                                    Or  -> (VFalse, state2)
                                    _   -> (VError "Operator Error : 06.", [])

                            _ ->
                                (VError "Operand Error : 04.", [])

                    VCons _ _ ->
                        case v2 of
                            VCons _ _ ->
                                if op == Cat then
                                    (appendValueList v1 v2, state2)
                                else if op == Eq then
                                    (if v1 == v2 then VTrue else VFalse, state2)
                                else
                                    (VError "Operator Error : 07.", [])
                            
                            VNil ->
                                if op == Cat then
                                    (appendValueList v1 v2, state2)
                                else if op == Eq then
                                    (VFalse, state2)
                                else
                                    (VError "Operator Error : 08.", [])
                            _ ->
                                (VError "Operand Error : 05.", [])

                    VNil ->
                        case v2 of
                            VCons _ _ ->
                                if op == Cat then
                                    (appendValueList v1 v2, state2)
                                else if op == Eq then
                                    (VFalse, state2)
                                else
                                    (VError "Operator Error : 09.", [])
                            
                            VNil ->
                                if op == Cat then
                                    (VNil, state2)
                                else if op == Eq then
                                    (VTrue, state2)
                                else
                                    (VError "Operator Error : 10.", [])
                            
                            _ ->
                                (VError "Operand Error : 07.", [])

                    VString _ _ ->
                        case v2 of
                            VString _ _ ->
                                if op == Cat then
                                    (appendValueString v1 v2, state2)
                                else if op == Eq then
                                    (if v1 == v2 then VTrue else VFalse, state2)
                                else
                                    (VError "Operator Error : 12.", [])

                            VEmpStr ->
                                if op == Cat then
                                    (appendValueString v1 v2, state2)
                                else if op == Eq then
                                    (VFalse, state2)
                                else
                                    (VError "Operator Error : 13.", [])

                            _ ->
                                (VError "Operand Error : 12.", [])

                    VEmpStr ->
                        case v2 of
                            VString _ _ ->
                                if op == Cat then
                                    (appendValueString v1 v2, state2)
                                else if op == Eq then
                                    (VFalse, state2)
                                else
                                    (VError "Operator Error : 14.", [])
                            
                            VEmpStr ->
                                if op == Cat then
                                    (VEmpStr, state2)
                                else if op == Eq then
                                    (VTrue, state2)
                                else
                                    (VError "Operator Error : 15.", [])

                            _ ->
                                (VError "Operand Error : 13.", [])

                    _ ->
                        (VError "Operand Error : 08.", [])

        TUPrim _ op t ->
            case op of
                Neg ->
                    let 
                        (v, state1) =
                            eval env state classtb t 
                    in
                        case v of
                            VInt n    ->
                                (VInt (0-n), state1)

                            VFloat n  ->
                                (VFloat (0-n), state1)

                            _         ->
                                (VError "Operand Error : 09.", [])
                Not ->
                    let 
                        (v, state1) =
                            eval env state classtb t 
                    in
                    case v of
                        VTrue     ->
                            (VFalse, state1)
                        
                        VFalse    ->
                            (VTrue, state1)
    
                        _         ->
                            (VError "Operand Error : 10.", [])

        TParens _ t ->
            eval env state classtb t

        TRef _ t ->
            let
                (v, state1) =
                    eval env state classtb t
            in
                (VLoc (List.length state1), state1++[v])

        TDeRef _ t ->
            let
                (v, state1) =
                    eval env state classtb t
            in
                case v of
                    VLoc n ->
                        case nth n state of
                            Just val ->
                                (val, state1)
                            
                            Nothing ->
                                (VError "Index Out Of Range : 01.", [])

                    _ -> (VError "Not a Reference : 01.", [])
                
        TAssign _ t1 t2 ->
            let
                (v1, state1) =
                    eval env state classtb t1
                
                (v2, state2) =
                    eval env state1 classtb t2
            in
                case v1 of
                    VLoc n ->
                        (VUnit, replace n v2 state2)


                    _ -> (VError "Not a Reference : 02.", [])

        TUnit _ -> (VUnit, state)

        TField _ t1 t2 ->
            case t2 of
                TVar _ f ->
                    let
                        (v1, state1) =
                            eval env state classtb t1
                    in
                        case v1 of
                        VNew class args ->
                            let
                                fields =
                                    getFields class classtb

                                index =
                                    findFieldsIndex f (List.indexedMap Tuple.pair fields)

                                val =
                                    findIndexValueList index args
                            in
                                case val of
                                    Just v -> (v, state1)

                                    Nothing -> (VError "No Such Field : 01.", [])

                        _ -> (VError "Not an Object : 01.", [])

                _ -> (VError "Not a Variable : 01.", [])

        TInvk _ t1 t2 ->
            case t2 of
                TVar _ m ->
                    let
                        (v1, state1) =
                            eval env state classtb t1
                    in
                        case v1 of
                            VNew class _ ->
                                let
                                    res =
                                        findMethod m class classtb
                                in
                                    case res of
                                        Just (_, (_, (_, p,t))) ->
                                            (VClosure p t (("this",v1)::env), state1)

                                        Nothing ->
                                            (VError "No Such Method : 01.", [])

                            _ -> (VError "Not an Object : 02.", [])

                _ ->
                    (VError "Not a Variable : 02.", [])

        TNew _ class ts ->
            let
                (vs, state1) =
                    eval env state classtb ts
            in
                (VNew class vs, state1)

        TError info -> (VError info, [])

        TSeq _ t1 t2 ->
            let
                (_, state1) =
                    eval env state classtb t1

                (v2, state2) =
                    eval env state1 classtb t2
            in
                (v2, state2)

        -- TLoc _ n -> (VLoc n, state)

        THtml _ s t1 t2 t3 ->
            let 
                (v1, state1) = 
                    eval env state classtb t1 

                (v2, state2) = 
                    eval env state1 classtb t2

                (v3, state3) = 
                    eval env state2 classtb t3
            in
                (VHtml s v1 v2 v3, state3)

        TToStr _ t ->
            let
                (v, state1) =
                    eval env state classtb t
            in
                (v |> printValue |> String.toList |> strToVString, state1)

        TMap _ _ f ls ->
            let
                (v1, state1) =
                    eval env state classtb f

                (v2, state2) =
                    eval env state1 classtb ls
            in
                vmap v1 v2 state2 classtb

        TLoc _ n ->
            (VLoc n, state)
        
        _ -> (VError "No Such Term : 01.", [])


boolOp : Bool -> Value
boolOp p =
    if p then VTrue else VFalse


intOp : Bop -> Int -> Int -> Value
intOp op n1 n2 =
    case op of
        -- Arith
        Add -> VInt (n1 + n2)
        Sub -> VInt (n1 - n2)
        Mul -> VInt (n1 * n2)
        Div -> VFloat (Round.roundNumCom 2 
                        <| ((toFloat n1) / (toFloat n2)))
        RDiv -> VInt (n1 // n2)
        -- Logic
        Eq -> boolOp (n1 == n2)
        Lt -> boolOp (n1 < n2)
        Gt -> boolOp (n1 > n2)
        Le -> boolOp (n1 <= n2)
        Ge -> boolOp (n1 >= n2)
        _  -> 
            VError "Operator Error : 01."


floatOp : Bop -> Float -> Float -> Value
floatOp op n1 n2 =
    case op of
        Add -> VFloat (Round.roundNumCom 2 <| n1 + n2)
        Sub -> VFloat (Round.roundNumCom 2 <| n1 - n2)
        Mul -> VFloat (Round.roundNumCom 2 <| n1 * n2)
        Div -> VFloat (Round.roundNumCom 2 <| n1 / n2)
        Eq -> boolOp (n1 == n2)
        Lt -> boolOp (n1 < n2)
        Gt -> boolOp (n1 > n2)
        Le -> boolOp (n1 <= n2)
        Ge -> boolOp (n1 >= n2)
        _  -> VError "Operator Error : 02."


vmap : Value -> Value -> State -> ClassTable -> (Value, State)
vmap v1 v2 state classtb =
    case v1 of
        VClosure p t envf ->
            case v2 of
                VCons v21 v22 ->
                    let 
                        envm =
                            match p v21
                    in
                    case envm of
                        [(_, VError info)] -> (VError info, [])
                        _             ->
                            let
                                (v21_, state1) =
                                    eval (envm++envf) state classtb t
                                
                                (v22_, state2) =
                                    vmap v1 v22 state1 classtb
                            in
                                (VCons v21_ v22_, state2)

                VNil ->
                    (VNil, state)

                _ ->
                    (VError "The third argument to map_ must be a list : 01.", [])

        _ ->
            (VError "The second argument to map_ must be a function : 01.", [])