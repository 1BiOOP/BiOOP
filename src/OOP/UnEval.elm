module OOP.UnEval exposing (..)

import Round
import List.Extra exposing (unconsLast, dropWhile)
import List exposing (..)
import OOP.Syntax exposing (..)
import OOP.Eval exposing (eval)
import OOP.Printer.Value exposing (printValue, printString)
import OOP.Printer.Term exposing (printTerm)
import OOP.LangUtils exposing (..)
import OOP.Utils exposing (updateValueInDict, findByName, replace)
import Utils exposing (nth)
import OOP.LangUtils exposing (mergeClassTable)
import OOP.Parser.Value as Value
import Debug exposing (toString)


type alias Context =
    { env : Env
    , state : State
    , classtb : ClassTable
    }


type alias Res =
    { value : Value
    , state : State
    }


uneval : Context -> Term -> Res -> (Context, Term)
uneval ctx term updates =
    case term of
        TInt ws _ ->
            case updates.value of
                VInt n -> 
                    ({ctx|state=updates.state}, TInt ws n)

                VFloat n ->
                    ({ctx|state=updates.state}, TFloat ws n)

                _ -> 
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TFloat ws _ ->
            case updates.value of
                VInt n ->
                    ({ctx|state=updates.state}, TFloat ws (toFloat n))

                VFloat n ->
                    ({ctx|state=updates.state}, TFloat ws n)

                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TTrue ws ->
            case updates.value of
                VTrue ->
                    ({ctx|state=updates.state}, TTrue ws)
                
                VFalse ->
                    ({ctx|state=updates.state}, TFalse ws)
                
                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TFalse ws->
            case updates.value of
                VTrue ->
                    ({ctx|state=updates.state}, TTrue ws)
                
                VFalse ->
                    ({ctx|state=updates.state}, TFalse ws)
                
                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TChar ws _ ->
            case updates.value of
                VChar c ->
                    ({ctx|state=updates.state}, TChar ws c)
                
                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        -- TString ws t1 t2 ->
        --     case updates.value of
        --         VString v1 v2 ->
        --             let
        --                 (_, state1) =
        --                     eval ctx.env ctx.state ctx.classtb t1

        --                 (ctx2, t2_) =
        --                     uneval {ctx|state=state1} t2 {value=v2,state=updates.state}

        --                 (ctx1, t1_) =
        --                     uneval ctx t1 {value=v1, state=ctx2.state}
        --             in
        --                 (ctx1, TString ws t1_ t2_)

        --         VEmpStr ->
        --             ({ctx|state=updates.state}, TEmpStr ws)

        --         _ ->
        --             (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TString _ _ _ ->
            let
                (origin_val, _) =
                    eval ctx.env ctx.state ctx.classtb term

                (_, delta) =
                    diff origin_val updates.value
            in
                deltaUpdate term delta ctx updates.state
        
        TEmpStr ws ->
            case updates.value of
                VEmpStr ->
                    ({ctx|state=updates.state}, TEmpStr ws)
                
                VString _ _ ->
                        ({ctx|state=updates.state}, valueToTerm updates.value ws)

                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TVar ws s ->
            let
                env_ =
                    updateValueInDict s updates.value ctx.env
            in
                ({ctx|env=env_,state=updates.state}, TVar ws s)

        TLam ws _ _ ->
            case updates.value of
                VClosure p_ t_ env_ ->
                    ({ctx|env=env_,state=updates.state}, TLam ws p_ t_)

                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TApp ws t1 (TFix _ t2) ->
            let 
                (v1, state1) = 
                    eval ctx.env ctx.state ctx.classtb t1
            in
            case v1 of
                VClosure p tf envf ->
                    case p of
                        PVar _ s  ->
                            let
                                (ctx1, tf_) =
                                    uneval {ctx|env=((s, VFix t2)::envf),state=state1} tf updates
                            in
                            case tf_  of
                                TError info ->
                                    (ctx, TError info)
                                
                                _ ->
                                    let 
                                        ctx1_env =
                                            dropWhile (\(s1,_) -> s1 /= s) ctx1.env
                                            |> drop 1

                                        newUpdates_1 =
                                            {value=VClosure p tf_ (ctx1_env), state=ctx1.state}
                                        
                                        (ctx_, t1_) =
                                            uneval ctx t1 newUpdates_1

                                        newClassTb =
                                            mergeClassTable ctx_.classtb ctx1.classtb ctx.classtb ctx.classtb
                                        
                                    in
                                    case t1_ of
                                        TError info ->
                                            (ctx, TError info)
                                        
                                        _ -> -- Magic Code
                                            case (findByName s ctx1.env) of
                                                Just (VClosure fixP fixT fixEnv) -> 
                                                    let
                                                        newUpdates_2 =
                                                            {value=VClosure fixP fixT fixEnv,state=[]}
                                                        
                                                        (_, t2_) =
                                                            uneval ctx (TFix [] t2) newUpdates_2
                                                    in
                                                        ({ctx_|classtb=newClassTb}, TApp ws t1_ t2_)
                                    
                                                Just (VFix t2_) ->
                                                    ({ctx_|classtb=newClassTb}, TApp ws t1_ (TFix [] t2_))
                                                
                                                Just (VError info) ->
                                                    ({ctx_|classtb=newClassTb}, TError info)
                                                
                                                Just error ->
                                                    (ctx, TError ("Fixpoint is Not a Function in Update : " ++ (printValue error)))
                                                
                                                Nothing ->
                                                    (ctx, TError "No Such Variable : 04.")
                        
                        _ ->
                            (ctx, TError "Pattern Error in Recursion : 01.")

                _ ->
                    (ctx, TError "Not Applicable : 02.")

        TApp ws t1 t2 ->
            let 
                (v1, state1) = 
                    eval ctx.env ctx.state ctx.classtb t1 
            in
            case v1 of
                VClosure p tf envf ->
                    let 
                        (v2, state2) =
                            eval ctx.env state1 ctx.classtb t2
                        
                        envm =
                            match p v2

                        (ctx2_, tf_) =
                            uneval {env=(envm++envf),state=state2,classtb=ctx.classtb} tf updates 
                    in
                    case tf_ of
                        TError info ->
                            (ctx, TError info)
                        
                        _ ->
                            let 
                                newUpdates_2 =
                                    {value = patternSubst ctx2_.env p, state=ctx2_.state}
                                
                                (ctx1_, t2_) =
                                    uneval  {ctx|state=state1} t2 newUpdates_2
                            in
                            case t2_ of
                                TError info ->
                                    (ctx, TError info)
                                
                                _ ->
                                    let
                                        newUpdates_1 =
                                            {value = VClosure p tf_ (drop (length envm) ctx2_.env),state=ctx1_.state}

                                        (ctx_, t1_) =
                                            uneval ctx t1 newUpdates_1
                                    in
                                    case t1_ of
                                        TError info ->
                                            (ctx, TError info)
                                        
                                        _ ->
                                            let
                                                newEnv =
                                                    mergeEnv ctx1_.env ctx_.env ctx.env

                                                newClassTb =
                                                    mergeClassTable ctx_.classtb ctx1_.classtb ctx2_.classtb ctx.classtb

                                            in
                                                ({env = newEnv
                                                , state = ctx_.state
                                                , classtb = newClassTb
                                                }
                                                , TApp ws t1_ t2_
                                                )
                                        
                _ ->
                    (ctx, TError "Not Appliable : 03.")

        TLet ws p t1 t2 ->
            let
                (ctx_, term_) =
                    uneval ctx (TApp [] (TLam [] p t2) t1) updates
            in
            case term_ of
                TError info ->
                    (ctx, TError info)

                TApp _ (TLam _ p_ t2_) t1_->
                    (ctx_, TLet ws p_ t1_ t2_)

                _ ->
                    (ctx, TError ("Wrong Result When Updating Let Statement : "++(printTerm term_)))
        
        TLetrec ws p t1 t2 ->
            let
                (ctx_, term_) =
                    uneval ctx (TApp [] (TLam [] p t2) (TFix [] (TLam [] p t1))) updates
            in
            case term_ of
                TError info ->
                    (ctx, TError info)

                TApp _ (TLam _ p_ t2_) (TFix _ (TLam _ _ t1_))->
                    (ctx_, TLetrec ws p_ t1_ t2_)

                _ ->
                    (ctx, TError ("Wrong Result When Updating Letrec Statement : "++(printTerm term_)))

        TFix ws t ->
            let
                (ctx_, t_) =
                    uneval ctx (TApp [] t (TFix [] t)) updates

                newT =
                    case t_ of
                        TApp _ t1 (TFix _ t2) ->
                            if t2 /= t then t2 else t1
                        _ ->
                            TError ("Wrong Result When Updating Letrec Statement : "++(printTerm t_))
            in
                (ctx_, TFix ws newT)

        TCase ws1 (TVar ws2 s) branches ->
            let
                res = 
                    findByName s ctx.env 
            in
            case res of
                Just v ->
                    let
                        matchRes =
                            matchCase v branches

                        (ctx_, ti_) =
                            uneval {ctx|env=(matchRes.envm++ctx.env)} matchRes.ti updates
                    in
                    case ti_ of
                        TError info ->
                            (ctx, TError info)

                        _ ->   
                            let 
                                branches_ =
                                    updateBranch branches matchRes.choice ti_
                                
                                len =
                                    length matchRes.envm

                                newV = matchRes.pi 
                                        |> patternSubst ctx_.env

                                env_ =
                                    ((s, newV) :: (drop (len + 1) ctx_.env))
                            in
                                ({ctx_|env=env_}, TCase ws1 (TVar ws2 s) branches_)
                
                Nothing ->
                    (ctx, TError "No Such Variable : 03.")

        TCons ws t1 t2 ->
            case updates.value of
                VCons v1 v2 ->
                    let
                        (_, state1) =
                            eval ctx.env ctx.state ctx.classtb t1

                        (ctx1_, t2_) =
                            uneval {ctx|state=state1} t2 {value=v2,state=updates.state}
                        
                        (ctx_, t1_) =
                            uneval ctx t1 {value=v1,state=ctx1_.state}

                        newEnv =
                            mergeEnv ctx1_.env ctx_.env ctx.env
                        
                        newClassTb =
                            mergeClassTable ctx1_.classtb ctx_.classtb ctx.classtb ctx.classtb

                    in
                        ({env=newEnv,state=ctx_.state,classtb=newClassTb}, TCons ws t1_ t2_)

                VNil ->
                    ({ctx|state=updates.state}, TNil ws)
                
                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TList _ _ _ ->
            let
                (origin_val, _) =
                    eval ctx.env ctx.state ctx.classtb term

                (_, delta) =
                    diff origin_val updates.value
            in
                deltaUpdate term delta ctx updates.state

        TNil ws ->
            case updates.value of
                VNil ->
                    ({ctx|state=updates.state}, TNil ws)

                VCons _ _ ->
                    ({ctx|state=updates.state}, valueToTerm updates.value ws)

                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TEmpList _ ->
            let
                (origin_val, _) =
                    eval ctx.env ctx.state ctx.classtb term

                (_, delta) =
                    diff origin_val updates.value
            in
                deltaUpdate term delta ctx updates.state
        
        TTuple2 ws t1 t2 ->
            case updates.value of
                VTuple2 v1 v2 ->
                    let
                        (_, state1) =
                            eval ctx.env ctx.state ctx.classtb t1

                        (ctx1_, t2_) =
                            uneval {ctx|state=state1} t2 {value=v2,state=updates.state}

                        (ctx_, t1_) =
                            uneval ctx t1 {value=v1,state=ctx1_.state}

                        newEnv =
                            mergeEnv ctx1_.env ctx_.env ctx.env

                        newClassTb =
                            mergeClassTable ctx1_.classtb ctx_.classtb ctx.classtb ctx.classtb
                    in
                        ({env=newEnv, state=ctx_.state, classtb=newClassTb}, TTuple2 ws t1_ t2_)
                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TTuple3 ws t1 t2 t3 ->
            case updates.value of
                VTuple3 v1 v2 v3 ->
                    let
                        (_, state1) =
                            eval ctx.env ctx.state ctx.classtb t1

                        (_, state2) =
                            eval ctx.env state1 ctx.classtb t2

                        (ctx2_, t3_) =
                            uneval {ctx|state=state2} t3 {value=v3,state=updates.state}

                        (ctx1_, t2_) =
                            uneval {ctx|state=state1} t2 {value=v2,state=ctx2_.state}

                        (ctx_, t1_) =
                            uneval ctx t1 {value=v1,state=ctx1_.state}

                        newEnv =
                            mergeEnv ctx2_.env (mergeEnv ctx1_.env ctx_.env ctx.env) ctx.env

                        newClassTb =
                            mergeClassTable ctx2_.classtb ctx1_.classtb ctx_.classtb ctx.classtb
                    in
                        ({env=newEnv, state=ctx_.state, classtb=newClassTb}, TTuple3 ws t1_ t2_ t3_)
                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TBPrim ws op t1 t2 ->
            let
                logic_ =
                    logic ctx t1 t2 updates ws

                arith_ = 
                    arith ctx t1 t2 updates ws

                comp_ = 
                    comp ctx t1 t2 updates ws
            in
            case op of
                And -> logic_ And

                Or  -> logic_ Or
                
                Add -> arith_ Add

                Sub -> arith_ Sub

                Mul -> arith_ Mul

                Div -> arith_ Div

                RDiv -> arith_ RDiv

                Cat -> arith_ Cat
                
                _ -> comp_ op
        
        TUPrim ws op t ->
            unevalUnaryOperation ctx op t updates ws

        TParens ws t ->
            let
                (ctx_, t_) =
                    uneval ctx t updates
            in
                (ctx_, TParens ws t_)

        TRef ws t ->
            case updates.value of
                VLoc n ->
                    case (nth n updates.state) of
                        Just newV ->
                            case (unconsLast updates.state) of
                                Just (_, state1) ->
                                    let
                                        (ctx_, t_) =
                                            uneval ctx t {value=newV,state=state1}
                                    in
                                        (ctx_, TRef ws t_)

                                Nothing ->
                                    (ctx, TError "Index Out of Range : 03.")

                        Nothing ->   
                            (ctx, TError "Index Out Of Range : 04.")

                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TDeRef ws t ->
            let
                (v1, _) =
                    eval ctx.env ctx.state ctx.classtb t
            in
            case v1 of
                VLoc n ->
                    case nth n ctx.state of
                        Just v2 ->
                            if v2 == updates.value then
                                let
                                    (ctx_, t_) =
                                        uneval ctx t {value=VLoc n,state=updates.state}
                                in
                                    (ctx_, TDeRef ws t_)
                            else
                                let
                                    newState =
                                        replace n updates.value updates.state                                    
                                    
                                    (ctx_, t_) =
                                        uneval ctx t {value=VLoc n,state=newState}
                                in
                                    (ctx_, TDeRef ws t_)

                        Nothing ->
                            (ctx, TError "Error : 35.")

                _ ->
                    (ctx, TError "Error : 05.")

        TAssign ws t1 t2 ->
            case updates.value of
                VUnit ->
                    let
                        (v1, state1) =
                            eval ctx.env ctx.state ctx.classtb t1
                        
                        (_, state2) =
                            eval ctx.env state1 ctx.classtb t2
                    in
                        case v1 of
                            VLoc n ->
                                case (nth n updates.state) of
                                    Just newV ->
                                        case (nth n state2) of
                                            Just oriV ->
                                                let
                                                    (ctx1_, t2_) =
                                                        uneval {ctx|state=state1} t2 {value=newV,state=replace n oriV updates.state}

                                                    (ctx_, t1_) =
                                                        uneval ctx t1 {value=VLoc n,state=ctx1_.state} 

                                                    newEnv =
                                                        mergeEnv ctx1_.env ctx_.env ctx.env
                                                    
                                                    newClassTb =
                                                        mergeClassTable ctx1_.classtb ctx_.classtb ctx.classtb ctx.classtb
                                                in
                                                    ({env=newEnv, state=ctx_.state, classtb=newClassTb}, TAssign ws t1_ t2_)

                                            Nothing ->
                                                (ctx, TError "Index Out Of Range : 06.")

                                    Nothing ->
                                        (ctx, TError "Index Out Of Range : 07.")

                            _ ->
                                (ctx, TError "Error : 15.")

                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))
        
        TUnit ws ->
            case updates.value of
                VUnit -> 
                    ({ctx|state=updates.state}, TUnit ws)
                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TField ws t1 t2 ->
            case t2 of
                TVar _ f ->
                    let
                        (v1, _) =
                            eval ctx.env ctx.state ctx.classtb t1
                    in
                        case v1 of
                            VNew class args ->
                                let
                                    fields =
                                        getFields class ctx.classtb

                                    index =
                                        findFieldsIndex f (List.indexedMap Tuple.pair fields)

                                    args_ =
                                        vreplace index updates.value args
                                in
                                case args_ of
                                    VError info ->
                                        (ctx, TError info)
                                    
                                    _ ->
                                        let
                                            (ctx_, t1_) =
                                                uneval ctx t1 {value=VNew class args_,state=updates.state}
                                        in
                                            (ctx_, TField ws t1_ t2)

                            _ ->
                                (ctx, TError "Not an Object : 03.")

                _ ->
                    (ctx, TError "Not a Variable : 03.")

        TInvk ws t1 t2 ->
            case t2 of
                TVar _ m ->
                    let
                        (v1, _) =
                            eval ctx.env ctx.state ctx.classtb t1
                    in
                        case v1 of
                            VNew class _ ->
                                let
                                    res =
                                        findMethod m class ctx.classtb
                                in
                                    case res of
                                        Just _ ->
                                            case updates.value of
                                                VClosure _ t_ env_ ->
                                                    let
                                                        newClassTb =
                                                            updateClassTable m class t_ ctx.classtb
                                                    in
                                                    case env_ of
                                                        ("this", newV_1)::_ ->
                                                            let
                                                                (ctx_, t1_) =
                                                                    uneval ctx t1 {value=newV_1,state=updates.state}
                                                            in
                                                                ({ctx_|classtb=newClassTb}, TInvk ws t1_ t2)
                                                        _ ->
                                                            (ctx, TError "Error : 06.")

                                                _ ->
                                                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

                                        Nothing ->
                                            (ctx, TError "No Such Method : 02.")

                            _ -> (ctx, TError "Not an Object : 04.")

                _ -> (ctx, TError "Not a Variable : 04.")

        TNew ws _ args ->
            case updates.value of
                VNew class_ vargs_ ->
                    let
                        (ctx_, args_) =
                            uneval ctx args {value=vargs_,state=updates.state}
                    in
                        (ctx_, TNew ws class_ args_)

                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TError info ->
            (ctx, TError info)

        TSeq ws t1 t2 ->
            let
                (v1, state1) =
                    eval ctx.env ctx.state ctx.classtb t1
                
                (ctx1_, t2_) =
                    uneval {ctx|state=state1} t2 updates
                
                (ctx_, t1_) =
                    uneval ctx t1 {value=v1,state=ctx1_.state}

                newEnv =
                    mergeEnv ctx1_.env ctx_.env ctx.env

                newClassTb =
                    mergeClassTable ctx1_.classtb ctx_.classtb ctx.classtb ctx.classtb
            in
                ({env=newEnv, state=ctx_.state, classtb=newClassTb}, TSeq ws t1_ t2_)

        THtml ws s t1 t2 t3 ->
            case updates.value of
                VHtml _ v1 v2 v3 ->
                    let
                        (_, state1) =
                            eval ctx.env ctx.state ctx.classtb t1

                        (_, state2) =
                            eval ctx.env state1 ctx.classtb t2

                        (ctx2_, t3_) =
                            uneval {ctx|state=state2} t3 {value=v3,state=updates.state}

                        (ctx1_, t2_) =
                            uneval {ctx|state=state1} t2 {value=v2,state=ctx2_.state}

                        (ctx_, t1_) =
                            uneval ctx t1 {value=v1,state=ctx1_.state}

                        newEnv =
                            mergeEnv ctx2_.env (mergeEnv ctx1_.env ctx_.env ctx.env) ctx.env

                        newClassTb =
                            mergeClassTable ctx2_.classtb ctx1_.classtb ctx_.classtb ctx.classtb
                    in
                        ({env=newEnv, state=ctx_.state, classtb=newClassTb}, THtml ws s t1_ t2_ t3_)
                
                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TToStr ws t ->
            case updates.value of
                VString _ _ ->
                    let
                        parseRes =
                            Value.parse (printString updates.value)
                    in
                    case parseRes of
                        Result.Ok newV ->
                            let
                                (ctx_, t_) =
                                    uneval ctx t {value=newV,state=updates.state}
                            in
                                (ctx_, TToStr ws t_)
                        
                        Result.Err info ->
                            (ctx, TError (toString info))

                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))

        TMap _ _ _ _ ->
            let
                (origin_val, _) =
                    eval ctx.env ctx.state ctx.classtb term
                
                (_, delta) =
                    diff origin_val updates.value
            in
                updateMap term delta ctx updates.state

        TLoc ws _ ->
            case updates.value of
                VLoc n_ ->
                    (ctx, TLoc ws n_)
                
                _ ->
                    (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm term)))
            
        _ -> (ctx, TError ("Source Expression Error : "++(printTerm term)))


logic : Context -> Term -> Term -> Res -> WS -> Bop -> (Context, Term)
logic ctx t1 t2 updates ws op =
    let
        (v1, state1) =
            eval ctx.env ctx.state ctx.classtb t1
        
        (v2, _) =
            eval ctx.env state1 ctx.classtb t2

        (vo, _) =
            eval ctx.env ctx.state ctx.classtb (TBPrim [] op t1 t2)
        
        (newV_1, newV_2) =
            case vo of
                VTrue ->
                    case updates.value of
                        VTrue -> (v1, v2)

                        VFalse ->
                            case (v1, v2, op) of
                                -- Heuristic, only modify t1
                                (VTrue, VTrue, And) ->
                                    (VFalse, VTrue)
                                
                                (VTrue, VTrue, Or) ->
                                    (VFalse, VFalse)

                                (VTrue, VFalse, Or) ->
                                    (VFalse, VFalse)

                                (VFalse, VTrue, Or) ->
                                    (VFalse, VFalse)

                                _ ->
                                    (VError "", VError "")
                        
                        _ ->
                            (VError "", VError "")
                
                VFalse ->
                    case updates.value of
                        VFalse -> (v1, v2)

                        VTrue ->
                            case (v1, v2, op) of
                                -- Heuristic, only modify t1
                                (VFalse, VFalse, Or) ->
                                    (VTrue, VFalse)

                                (VFalse, VFalse, And) ->
                                    (VTrue, VTrue)

                                (VTrue, VFalse, And) ->
                                    (VTrue, VTrue)

                                (VFalse, VTrue, And) ->
                                    (VTrue, VTrue)

                                _ ->
                                    (VError "", VError "")

                        _ ->
                            (VError "", VError "")
                
                _ ->
                    (VError "", VError "")
    in
    case (newV_1, newV_2) of
        (VError _, VError _) ->
            (ctx, TError ("Wrong Logic Expression : "++(printTerm (TBPrim ws op t1 t2))))

        _ ->
            operationUpdate ctx op t1 t2 updates newV_1 newV_2 ws


arith : Context -> Term -> Term -> Res -> WS -> Bop -> (Context, Term)
arith ctx t1 t2 updates ws op =
    let
        (v1, state1) =
            eval ctx.env ctx.state ctx.classtb t1
        
        (v2, _) =
            eval ctx.env state1 ctx.classtb t2
    in
    case updates.value of
        VInt n ->
            let
                (newV_1, newV_2) =
                    case (v1, v2) of
                        (VFloat n1, _) ->
                            case op of
                                Add -> (VFloat n1, VFloat (Round.roundNumCom 2 <| (toFloat n) - n1))

                                Sub -> (VFloat n1, VFloat (Round.roundNumCom 2 <| n1 - (toFloat n)))

                                Mul -> (VFloat n1, VFloat (Round.roundNumCom 2 <| (toFloat n) / n1))

                                Div -> (VFloat n1, VFloat (Round.roundNumCom 2 <| n1 / (toFloat n)))

                                _   -> (VError "", VError "")
                        
                        (_, VFloat n2) ->
                            case op of
                                Add -> (VFloat (Round.roundNumCom 2 <| (toFloat n) - n2), VFloat n2)

                                Sub -> (VFloat (Round.roundNumCom 2 <| (toFloat n) + n2), VFloat n2)

                                Mul -> (VFloat (Round.roundNumCom 2 <| (toFloat n) / n2), VFloat n2)

                                Div -> (VFloat (Round.roundNumCom 2 <| (toFloat n) * n2), VFloat n2)

                                _   -> (VError "", VError "")
                        
                        (VInt n1, VInt n2) ->
                            case op of
                                Add -> (VInt n1, VInt (n - n1))

                                Sub -> (VInt n1, VInt (n1 - n))

                                Mul ->
                                    if (n1 * n2) == n then
                                        (VInt n1, VInt n2)
                                    else if (modBy n1 n == 0) then
                                        (VInt n1, VInt (n // n1))
                                    else
                                        (VInt n1, VFloat (Round.roundNumCom 2 <| (toFloat n) / (toFloat n1)))

                                Div ->
                                    if (n1 // n2) == n && modBy n2 n1 == 0 then
                                        (VInt n1, VInt n2)
                                    else if (modBy n n1 == 0) then
                                        (VInt n1, VInt (n1 // n))
                                    else
                                        (VInt n1, VFloat ((toFloat n1) / (toFloat n)))

                                RDiv ->
                                    if (n1 // n2) == n then
                                        (VInt n1, VInt n2)
                                    else
                                        (VInt n1, VInt (n1 // n))

                                _   -> (VError "", VError "")
                        
                        _ -> (VError "", VError "")
            in
            case (newV_1, newV_2) of
                (VError _, VError _) ->
                    (ctx, TError ("Wrong Arith Expression : "++(printTerm (TBPrim ws op t1 t2))))

                _ ->
                    operationUpdate ctx op t1 t2 updates newV_1 newV_2 ws

        VFloat n ->
            let
                (newV_1, newV_2) =
                    case (v1, v2) of
                        
                        (VFloat n1, _) ->
                            case op of
                                Add -> (VFloat n1, VFloat (Round.roundNumCom 2 <| n - n1))

                                Sub -> (VFloat n1, VFloat (Round.roundNumCom 2 <| n1 - n))

                                Mul -> (VFloat n1, VFloat (Round.roundNumCom 2 <| n / n1))

                                Div -> (VFloat n1, VFloat (Round.roundNumCom 2 <| n1 / n))

                                _   -> (VError "", VError "")
                        
                        (_, VFloat n2) ->
                            case op of
                                Add -> (VFloat (Round.roundNumCom 2 <| n - n2), VFloat n2)

                                Sub -> (VFloat (Round.roundNumCom 2 <| n + n2), VFloat n2)

                                Mul -> (VFloat (Round.roundNumCom 2 <| n / n2), VFloat n2)

                                Div -> (VFloat (Round.roundNumCom 2 <| n * n2), VFloat n2)

                                _   -> (VError "", VError "")

                        (VInt n1, VInt n2) ->
                            case op of
                                Add -> (VInt n1, VFloat (Round.roundNumCom 2 <| n - (toFloat n1)))

                                Sub -> (VInt n1, VFloat (Round.roundNumCom 2 <| (toFloat n1) - n))

                                Mul ->
                                    if (toFloat <| n1 * n2) == n then
                                        (VInt n1, VInt n2)
                                    else
                                        (VInt n1, VFloat (Round.roundNumCom 2 <| n / (toFloat n1)))

                                Div ->
                                    if ((toFloat n1) / (toFloat n2)) == n then
                                        (VInt n1, VInt n2)
                                    else
                                        (VInt n1, VFloat ((toFloat n1) / n))

                                RDiv ->
                                    if (toFloat <| n1 // n2) == n then
                                        (VInt n1, VInt n2)
                                    else
                                        (VInt n1, VInt (truncate <| (toFloat n1) / n))

                                _   -> (VError "", VError "")
                        
                        _ -> (VError "", VError "")
            in
            case (newV_1, newV_2) of
                (VError _, VError _) ->
                    (ctx, TError ("Wrong Arith Expression : "++(printTerm (TBPrim ws op t1 t2))))

                _ ->
                    operationUpdate ctx op t1 t2 updates newV_1 newV_2 ws

        VCons _ _ ->
            if op == Cat then
                let
                    (newV_1, newV_2) =
                        vsplit updates.value (vlength v1)
                in
                    operationUpdate ctx op t1 t2 updates newV_1 newV_2 ws
            else
                (ctx, TError "Operator Error : 11.")

        VNil ->
            if op == Cat then
                operationUpdate ctx op t1 t2 updates VNil VNil ws
            else
                (ctx, TError "Operator Error : 12.")

        VString _ _ ->
            if op == Cat then
                let
                    (newV_1, newV_2) =
                        vsplit updates.value ((vlength updates.value) - (vlength v2))
                in
                    operationUpdate ctx op t1 t2 updates newV_1 newV_2 ws
            else
                (ctx, TError "Operator Error : 16.")

        VEmpStr ->
            if op == Cat then
                operationUpdate ctx op t1 t2 updates VNil VNil ws
            else
                (ctx, TError "Operator Error : 17.")

        _ -> 
            (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm (TBPrim ws op t1 t2))))


comp : Context -> Term -> Term -> Res -> WS -> Bop -> (Context, Term)
comp ctx t1 t2 updates ws op =
    let
        (v1, _) =
            eval ctx.env ctx.state ctx.classtb t1
    in
    case updates.value of
        VTrue ->
            case op of
                Eq ->
                    operationUpdate ctx op t1 t2 updates v1 v1 ws

                _ ->
                    let
                        (vo, _) =
                            eval ctx.env ctx.state ctx.classtb (TBPrim [] op t1 t2)
                        
                        newTerm =
                            case vo of
                                VTrue -> TBPrim ws op t1 t2
                                VFalse ->
                                    case op of
                                        Lt -> TBPrim ws Ge t1 t2
                                        Gt -> TBPrim ws Le t1 t2
                                        Le -> TBPrim ws Gt t1 t2
                                        Ge -> TBPrim ws Lt t1 t2
                                        _  ->
                                            TError ""
                                _ ->
                                    TError ("Error : 01.")
                    in
                        ({ctx|state=updates.state}, newTerm)

        VFalse ->
            let
                (vo, _) =
                            eval ctx.env ctx.state ctx.classtb (TBPrim [] op t1 t2)
                
                newTerm =
                    case vo of
                        VFalse -> TBPrim ws op t1 t2
                        VTrue ->
                            case op of
                                Lt -> TBPrim ws Ge t1 t2
                                Gt -> TBPrim ws Le t1 t2
                                Le -> TBPrim ws Gt t1 t2
                                Ge -> TBPrim ws Lt t1 t2
                                Eq -> TError ("Cannot Infer : "++(printValue updates.value)++"->"++(printTerm (TBPrim ws op t1 t2)))
                                _  -> TError ""
                        _ ->
                            TError ("Error : 02.")
            in
                ({ctx|state=updates.state}, newTerm)

        _ ->
            (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm (TBPrim ws op t1 t2))))


operationUpdate : Context -> Bop -> Term -> Term -> Res -> Value -> Value -> WS -> (Context, Term)
operationUpdate ctx op t1 t2 updates newV_1 newV_2 ws =
    let
        (_, state1) =
            eval ctx.env ctx.state ctx.classtb t1
        
        (ctx1_, t2_) =
            uneval {ctx|state=state1} t2 {value=newV_2,state=updates.state}

        (ctx_, t1_) =
            uneval ctx t1 {value=newV_1, state=ctx1_.state}
        
        newEnv =
            mergeEnv ctx_.env ctx1_.env ctx.env

        newClassTb =
            mergeClassTable ctx1_.classtb ctx_.classtb ctx.classtb ctx.classtb
    in
        ({env=newEnv, state=ctx_.state, classtb=newClassTb}, TBPrim ws op t1_ t2_)


unevalUnaryOperation : Context -> Uop -> Term -> Res -> WS -> (Context, Term)
unevalUnaryOperation ctx op t updates ws =
    let 
        (v, _) = 
            eval ctx.env ctx.state ctx.classtb t
    in
    case op of
        Not ->
            case v of
                VTrue ->
                    case updates.value of
                        VTrue ->
                            let
                                (ctx_, t_) =
                                    uneval ctx t {value=VFalse,state=updates.state}
                            in
                                (ctx_, TUPrim ws op t_)

                        VFalse ->
                            ({ctx|state=updates.state}, TUPrim ws op t)

                        _ -> 
                            (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm (TUPrim ws op t))))

                VFalse ->
                    case updates.value of
                        VTrue ->
                            ({ctx|state=updates.state}, TUPrim ws op t)

                        VFalse ->
                            let
                                (ctx_, t_) =
                                    uneval ctx t {value=VTrue,state=updates.state}
                            in
                                (ctx_, TUPrim ws op t_)

                        _ -> 
                            (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm (TUPrim ws op t))))
                
                _ ->
                    (ctx, TError "Error : 03.")

        Neg ->
            case v of
                VInt n ->
                    case updates.value of
                        VInt n_ ->
                            if n == (-n_) then 
                                ({ctx|state=updates.state}, TUPrim ws op t)
                            else
                                let
                                    (ctx_, t_) =
                                        uneval ctx t {value=VInt (-n_),state=updates.state}
                                in
                                    (ctx_, TUPrim ws op t_)

                        VFloat n_ ->
                            if (toFloat n) == -n_ then 
                                ({ctx|state=updates.state}, TUPrim ws op t)
                            else
                                let
                                    (ctx_, t_) =
                                        uneval ctx t {value=VFloat (-n_),state=updates.state}
                                in
                                    (ctx_, TUPrim ws op t_)

                        _ -> 
                            (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm (TUPrim ws op t))))

                VFloat n ->
                    case updates.value of
                        VInt n_ ->
                            if n == toFloat (-n_) then 
                                ({ctx|state=updates.state}, TUPrim ws op t)
                            else
                                let
                                    (ctx_, t_) =
                                        uneval ctx t {value=VFloat (toFloat (-n_)),state=updates.state}
                                in
                                    (ctx_, TUPrim ws op t_)

                        VFloat n_ ->
                            if n == (-n_) then 
                                ({ctx|state=updates.state}, TUPrim ws op t)
                            else
                                let
                                    (ctx_, t_) =
                                        uneval ctx t {value=VFloat (-n_),state=updates.state}
                                in
                                    (ctx_, TUPrim ws op t_)

                        _ -> 
                            (ctx, TError ("Update Error : "++(printValue updates.value)++"->"++(printTerm (TUPrim ws op t))))

                
                _ ->
                    (ctx, TError "Error : 04.")


deltaUpdate : Term -> List DiffOp -> Context -> State -> (Context, Term)
deltaUpdate term delta ctx newState =
    case term of
        TList ws t1 t2 ->
            case delta of
                Keep :: resDelta ->
                    let
                        (v1, state1) =
                            eval ctx.env ctx.state ctx.classtb t1

                        (ctx1_, t2_) =
                            deltaUpdate t2 resDelta {ctx|state=state1} newState

                        -- in case there is an assignment in t1
                        (ctx_, t1_) =
                            uneval ctx t1 {value=v1, state=ctx1_.state}

                        newEnv =
                            mergeEnv ctx_.env ctx1_.env ctx.env

                        newClassTb =
                            mergeClassTable ctx_.classtb ctx1_.classtb ctx.classtb ctx.classtb
                    in
                        ({ctx_|env=newEnv,classtb=newClassTb}, TList ws t1_ t2_)
                
                Delete :: resDelta ->
                    let
                        (v1, state1) =
                            eval ctx.env ctx.state ctx.classtb t1
                    
                        -- Deleting t1 means also deleting the side effects in t1
                        (ctx1_, t2_) =
                            deltaUpdate t2 resDelta {ctx|state=state1} newState

                        (ctx_, _) = 
                            uneval ctx t1 {value=v1, state=ctx1_.state}
                    in
                        case t2_ of
                            TList _  t ts ->
                                ({ctx1_|state=ctx_.state}, TList ws t ts)
                            
                            TEmpList _ ->
                                ({ctx1_|state=ctx_.state}, TEmpList ws)
                        
                            _ ->
                                (ctx, TError "Error : 31.")
                    -- let
                    --     (_, state1) =
                    --         eval ctx.env ctx.state ctx.classtb t1
                    
                    --     -- Deleting t1 means also deleting the side effects in t1
                    --     (ctx_, t2_) =
                    --         deltaUpdate t2 resDelta {ctx|state=state1} newState

                    --     state_ = take (length ctx.state) ctx_.state
                    -- in
                    --     case t2_ of
                    --         TList _  t ts ->
                    --             ({ctx_|state=state_}, TList ws t ts)
                            
                    --         TEmpList _ ->
                    --             ({ctx_|state=state_}, TEmpList ws)
                        
                    --         _ ->
                    --             (ctx, TError "Error : 31.")
                
                (Insert v) :: resDelta ->
                    let
                        (ctx_, term_) =
                            deltaUpdate term resDelta ctx newState

                        t_ =
                            case v of
                                VCons _ _ ->
                                    valueToTerm v ["", ""]

                                _ ->
                                    valueToTerm v [""]
                    in
                        (ctx_, TList ws t_ term_)
                
                (Update v) :: resDelta ->
                    let
                        (_, state1) =
                            eval ctx.env ctx.state ctx.classtb t1

                        (ctx1_, t2_) =
                            deltaUpdate t2 resDelta {ctx|state=state1} newState

                        (ctx_, t1_) =
                            uneval ctx t1 {value=v, state=ctx1_.state}
                        newEnv =
                            mergeEnv ctx_.env ctx1_.env ctx.env

                        newClassTb =
                            mergeClassTable ctx_.classtb ctx1_.classtb ctx.classtb ctx.classtb

                    in
                        ({ctx_|env=newEnv, classtb=newClassTb}, TList ws t1_ t2_)

                [] ->
                    (ctx, TError "Diff Solve Error : 01.")

        TEmpList ws ->
            case delta of
                (Insert v) :: resDelta ->
                    let
                        (ctx_, term_) =
                            deltaUpdate term resDelta ctx newState

                        t_ =
                            case v of
                                VCons _ _ ->
                                    valueToTerm v ["", ""]

                                _ ->
                                    valueToTerm v [""]               
                    in
                        (ctx_, TList ws t_ term_)

                [] ->
                    ({ctx|state=newState}, TEmpList ws)
                
                _ ->
                    (ctx, TError "Diff Solve Error : 02.")

        TString ws t1 t2 ->
            case delta of
                Keep :: resDelta ->
                    let
                        (v1, state1) =
                            eval ctx.env ctx.state ctx.classtb t1

                        (ctx1_, t2_) =
                            deltaUpdate t2 resDelta {ctx|state=state1} newState

                        -- in case there is an assignment in t1
                        (ctx_, _) =
                            uneval ctx t1 {value=v1, state=ctx1_.state}
                    in
                        ({ctx1_|state=ctx_.state}, TString ws t1 t2_)
                
                Delete :: resDelta ->
                    let
                        -- Deleting t1 means also deleting the side effects in t1
                        (ctx_, t2_) =
                            deltaUpdate t2 resDelta ctx newState
                    in
                        case t2_ of
                            TString _  t ts ->
                                    (ctx_, TString ws t ts)
                                
                            TEmpStr _ ->
                                    (ctx_, TEmpStr ws)
                                
                            _ ->
                                (ctx, TError "Error : 32.")
                
                (Insert v) :: resDelta ->
                    let
                        (ctx_, term_) =
                            deltaUpdate term resDelta ctx newState

                        t_ =
                            valueToTerm v [""]
                    in
                        (ctx_, TString ws t_ term_)
                
                (Update v) :: resDelta ->
                    let
                        (_, state1) =
                            eval ctx.env ctx.state ctx.classtb t1

                        (ctx1_, t2_) =
                            deltaUpdate t2 resDelta {ctx|state=state1} newState

                        (ctx_, t1_) =
                            uneval ctx t1 {value=v, state=ctx1_.state}

                    in
                        (ctx_, TString ws t1_ t2_)

                [] ->
                    (ctx, TError "Diff Solve Error : 03.")
        
        TEmpStr ws ->
            case delta of
                (Insert v) :: resDelta ->
                    let
                        (ctx_, term_) =
                            deltaUpdate term resDelta ctx newState
                        t_ =
                            valueToTerm v [""]
                    in
                        (ctx_, TString ws t_ term_)

                [] ->
                    ({ctx|state=newState}, TEmpStr ws)
                
                _ ->
                    (ctx, TError "Diff Solve Error : 04.")

        _ ->
            (ctx, TError "Delta Update is only available for lists and strings.")


updateMap : Term -> List DiffOp -> Context -> State -> (Context, Term)
updateMap term delta ctx newState =
    case term of
        TMap ws d f ls ->
            let
                (v1, state1) =
                    eval ctx.env ctx.state ctx.classtb f

                (v2, _) =
                    eval ctx.env state1 ctx.classtb ls
            in
            case v2 of
                VCons _ _ ->
                    let
                        res =
                            updateMapHelper v1 v2 delta ctx newState state1 f ls d
                    in
                        (Tuple.first res, TMap ws d f (Tuple.second res))

                VNil ->
                    let
                        res =
                            updateMapHelper v1 v2 delta ctx newState state1 f ls d
                    in
                        (Tuple.first res, TMap ws d f (Tuple.second res))

                _ ->
                    (ctx, TError "The third argument to map_ must be a list : 02.")

        _ ->
            (ctx, TError "Error : 26.")


updateMapHelper : Value -> Value -> List DiffOp -> Context -> State -> State ->
                    Term -> Term -> Term -> (Context, Term)
updateMapHelper v1 v2 delta ctx newState state1 f ls d =
    let
        v2_ =
            updateMap_ f v2 delta ctx d newState

        (ctx1_, ls_) =
            uneval {ctx|state=state1} ls {value=v2_, state=newState}

        (ctx_, _) =
            uneval ctx f {value=v1, state=ctx1_.state}

        newEnv =
            mergeEnv ctx1_.env ctx_.env ctx.env

        newClassTb =
            mergeClassTable ctx1_.classtb ctx_.classtb ctx.classtb ctx.classtb
    in
        ({ctx_|env=newEnv, classtb=newClassTb}, ls_)


updateMap_ : Term -> Value -> List DiffOp -> Context -> Term -> State -> Value
updateMap_ f v delta ctx default newState =
    case v of
        VCons v1 v2 ->
            case delta of
                Keep :: resDelta ->
                    let
                        v2_ =
                            updateMap_ f v2 resDelta ctx default newState
                    in
                        VCons v1 v2_
                
                Delete :: resDelta ->
                    updateMap_ f v2 resDelta ctx default newState
                
                (Insert v_) :: resDelta ->
                    let
                        v2_ =
                            updateMap_ f v resDelta ctx default newState

                        (_, res) =
                            uneval ctx (TApp [] f default) {value=v_,state=newState}
                    in
                        case res of
                            TApp _ _ default_ ->
                                let
                                    (v1_, _) =
                                        eval [] [] ([],[]) default_
                                in
                                    VCons v1_ v2_

                            _ ->
                                VError "Error : 28."
                
                (Update v_) :: resDelta ->
                    let
                        v2_ =
                            updateMap_ f v2 resDelta ctx default newState

                        (_, res) =
                            uneval ctx (TApp [] f default) {value=v_,state=newState}
                    in
                        case res of
                            TApp _ _ default_ ->
                                let
                                    (v1_, _) =
                                        eval [] [] ([],[]) default_
                                in
                                    VCons v1_ v2_

                            _ ->
                                VError "Error : 29."

                [] ->
                    VError "Diff Solve Error : 05."

        VNil ->
            case delta of
                (Insert v_) :: resDelta ->
                        let
                            v2_ =
                                updateMap_ f VNil resDelta ctx default newState

                            (_, res) =
                                uneval ctx (TApp [] f default) {value=v_,state=newState}
                        in
                            case res of
                                TApp _ _ default_ ->
                                    let
                                        (v1_, _) =
                                            eval [] [] ([],[]) default_
                                    in
                                        VCons v1_ v2_

                                _ ->
                                    VError "Error : 30."

                [] ->
                    VNil
                
                _ ->
                    VError "Diff Solve Error : 06."

        _ ->
            VError "Error : 27."