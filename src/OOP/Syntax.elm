module OOP.Syntax exposing (..)

type OOP
    = WithCT ClassTable Term
    | NoCT Term

type Term 
    = TInt WS Int
    | TFloat WS Float
    | TTrue WS
    | TFalse WS
    | TChar WS Char
    | TString WS Term Term
    | TEmpStr WS
    | TVar WS String
    | TLam WS Pattern Term
    | TApp WS Term Term
    | TLet WS Pattern Term Term
    | TLetrec WS Pattern Term Term
    | TFix WS Term
    | TCase WS Term Branch
    | TCons WS Term Term
    | TList WS Term Term
    | TNil WS
    | TEmpList WS
    | TTuple2 WS Term Term
    | TTuple3 WS Term Term Term
    | TBPrim WS Bop Term Term
    | TUPrim WS Uop Term
    | TParens WS Term
    | TRef WS Term
    | TDeRef WS Term
    | TAssign WS Term Term
    | TUnit WS
    | TField WS Term Term
    | TInvk WS Term Term
    | TNew WS String Term
    | TError Info
    | TSeq WS Term Term
    | THtml WS String Term Term Term
    | TToStr WS Term
    | TMap WS Term Term Term
    | TLoc WS Int

-- Div : Divide ; RDiv: Divide Rounding
type Bop = Add | Sub | Mul | Div | Eq | Lt | Gt | Le | Ge | And | Or | Cat | RDiv
type Uop = Not | Neg

type Value
    = VInt Int
    | VFloat Float
    | VTrue
    | VFalse
    | VChar Char
    | VString Value Value
    | VEmpStr
    | VCons Value Value
    | VNil
    | VFix Term
    | VClosure Pattern Term Env
    | VTuple2 Value Value
    | VTuple3 Value Value Value
    | VLoc Int
    | VUnit
    | VNew String Value
    | VError Info
    | VHtml String Value Value Value

type Pattern
    = PVar WS String
    | PCons WS Pattern Pattern
    | PNil WS
    | PList WS Pattern Pattern
    | PEmpList WS
    | PInt WS Int
    | PFloat WS Float
    | PTrue WS
    | PFalse WS
    | PString WS Pattern Pattern
    | PEmpStr WS
    | PChar WS Char
    | PBTuple WS Pattern Pattern
    | PTTuple WS Pattern Pattern Pattern
    | PUnit WS
    | PError

type Branch
    = BSin WS Pattern Term
    | BNSin WS ID Pattern Term
    | BCom WS Branch Branch

type alias Env = List (String, Value)
type alias State = List Value
type alias Method = (WS, (String, Pattern, Term))
type alias Methods = (WS, List Method)
-- (field, type)
-- String, Int, Float, Bool, List_X
type alias Fields = (WS, List (WS, String, String))
type alias ClassDef = (WS, ((String, String), Fields, Methods))
type alias ClassTable = (WS, List ClassDef)
type alias Info = String
type alias ID = Int

type alias WS = List String

-- Case
guardName : String
guardName = "$CASE$"

type alias MatchCaseRes =
    { envm : Env
    , choice: Int
    , ti : Term
    , pi : Pattern
    }

defaultClassTable : ClassTable
defaultClassTable =
    ([], [([], (("Object", "Object"), ([],[]), ([],[])))])


type DiffOp = Keep | Delete | Insert Value | Update Value