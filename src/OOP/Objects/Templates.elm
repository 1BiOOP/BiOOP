module OOP.Objects.Templates exposing (..)

import Debug exposing (toString)
import OOP.Parser.Term exposing (parse)
import OOP.Syntax exposing (Term(..), Env)

type alias Class = String
type alias ObjectPat = Term
type alias HtmlPat = Term
type alias ObjectID = Int
type alias FieldID = Int
type alias EnvDict = List (ObjectID, Env)

type alias Template =
    { class : String
    , oPat : ObjectPat
    , hPat : HtmlPat
    }

type alias Templates = List Template


-- When writing a script, cannot add any attributes.
-- Because the parser for html in Elm will parse strange results.
templates : List (String, String, String)
templates = 
    [  
        ( "Input"
        , "new Input([name, hint])"
        , """Html.input [] [["name", name]] []"""),

        ( "TextField"
        , "new TextField([name, hint, left])"
        , """Html.p [ ["margin-left", left]
                    , ["text-align", "left"]
                    ] 
                    [] 
                    [ hint
                    ,  Html.input [] [["type", "text"]
                                    , ["name", name]] []
                    ]"""),

        ( "PasswordField"
        , "new PasswordField([name, hint, left])"
        , """Html.p [ ["margin-left", left]
                    , ["text-align", "left"]
                    ] 
                    [] 
                    [ hint
                    , Html.input [] [["type", "password"]
                                    ,["name", name]] []
                    ]"""),

        ( "RadioButton"
        , "new RadioButton([name, hint, value])"
        , """Html.div [] [] [ Html.input [] [ ["type", "radio"]
                                            , ["name", name]
                                            , ["value", value]] []
                            , hint
                            ]"""),
        
        ( "CheckBox"
        , "new CheckBox([name, hint, value])"
        , """Html.div [] [] [ Html.input [] [ ["type", "checkbox"]
                                            , ["name", name]
                                            , ["value", value]] []
                            , hint]"""),

        ( "SubmitButton"
        , "new SubmitButton([name, hint, value])"
        , """Html.input [] [  ["type", "submit"]
                            , ["name", name]
                            , ["value", value]] []"""),

        ( "Form"
        , "new Form([id, inputs, dataProcess])"
        , """Html.div [] [] [ Html.form [] [["id", id]] inputs
                            , Html.script [] [] 
                                        ["  var form = document.getElementById('"++id++"');
                                            form.addEventListener('submit', (ev)=>{
                                                ev.preventDefault();
                                                const data = new FormData(form);" 
                                                ++ dataProcess ++ "});"]
                            ]"""),

        ( "NewLine"
        , "new NewLine([])"
        , "Html.br [] [] []"),

        ( "TextPane"
        , "new TextPane([id])"
        , """Html.textarea [] [["id", id]] []"""),

        ( "WebPage"
        , "new WebPage([components])"
        , "Html.div [] [] components"),

        ( "Coffee"
        , "new Coffee([id, price, count])"
        , """Html.div [["display", "flex"]] []  [ Html.div  [ ["width", "100px"]
                                                            , ["border-bottom", "1px blue solid"]] [] [id]
                                                , Html.div  [ ["width", "50px"]
                                                            , ["border-bottom", "1px blue solid"]] [] [price]
                                                , Html.div  [ ["width", "50px"]
                                                            , ["border-bottom", "1px blue solid"]] [] [count]]"""),

        ( "DisplayArea2"
        , "new DisplayArea2([menu])"
        , """Html.div   [["margin-bottom", "50px"]] [] 
                        [ Html.div  [["display", "flex"]] []  
                                    [ Html.div  [ ["width", "100px"]
                                                , ["border-bottom", "1px blue solid"]] [] ["Name"]
                                    , Html.div  [ ["width", "50px"]
                                                , ["border-bottom", "1px blue solid"]] [] ["Price"]
                                    , Html.div  [ ["width", "50px"]
                                                , ["border-bottom", "1px blue solid"]] [] ["Count"]]
                        , Html.div [] [] menu]"""),

        ( "ConfirmArea"
        , "new ConfirmArea([menu, total])"
        , """Html.div [] [] [ Html.div [["text-align", "left"]] [] ["Please confirm your order:"]
                            , Html.div  [["display", "flex"]] []  
                                        [ Html.div  [ ["width", "100px"]
                                                    , ["border-bottom", "1px blue solid"]] [] ["Name"]
                                        , Html.div  [ ["width", "50px"]
                                                    , ["border-bottom", "1px blue solid"]] [] ["Price"]
                                        , Html.div  [ ["width", "50px"]
                                                    , ["border-bottom", "1px blue solid"]] [] ["Count"]]
                            , Html.div [] [] menu
                            , Html.div [["text-align", "left"]] [] ["total: " ++ total]]"""),
        
        ( "Cafe"
        , "new Cafe([slogan, coffeeArea, confirmArea])"
        , """Html.div [] [] [ Html.div [] [] [slogan]
                            , coffeeArea
                            , confirmArea]""")
    ]


parseTemplates : List (String, String, String) -> Templates
parseTemplates tplt =
    case tplt of
        (cl, op, hp) :: rest ->
            let
                res1 =
                    parse op

                res2 =
                    parse hp
            in
                case (res1, res2) of
                    (Result.Ok objectPat, Result.Ok htmlPat) ->
                        {class=cl, oPat=objectPat, hPat=htmlPat} :: (parseTemplates rest)

                    (_, Result.Err info) ->
                        [{class=cl, oPat=TError "", hPat=TError (toString info)}]
                    
                    (Result.Err info, _) ->
                        [{class=cl, oPat=TError (toString info), hPat=TError ""}]

        [] ->
            []


findTemplateByClass : String -> Templates -> Maybe (ObjectPat, HtmlPat)
findTemplateByClass class temps =
    case temps of
        temp :: rest ->
            if temp.class == class then
                Just (temp.oPat, temp.hPat)
            else
                findTemplateByClass class rest

        [] -> Nothing