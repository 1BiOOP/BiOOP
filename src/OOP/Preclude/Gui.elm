module OOP.Preclude.Gui exposing (..)

import OOP.Syntax exposing (ClassTable)
import OOP.Parser.ClassTable exposing (parse)

guiLibrary : String
guiLibrary =
    """Class Frame Extends Object {}

    Class Input Extends Object {
        name:String, hint:String;
    }

    Class TextField Extends Input {
        left:String;
    }

    Class PasswordField Extends TextField {}

    Class RadioButton Extends Input {
        value:String;
    }

    Class CheckBox Extends Input {
        value:String;
    }

    Class SubmitButton Extends Input {
        value:String;
    }

    Class Form Extends Frame {
        id:String, inputs:List<Input>, dataProcess:String;
    }

    Class NewLine Extends Object {}

    Class TextPane Extends Frame {
        id:String;
    }

    Class WebPage Extends Object {
        components:List<Frame>;
    }
    """


parsedGui : ClassTable
parsedGui =
    case parse guiLibrary of
        Result.Ok clt -> 
            clt
        
        Result.Err _ ->
            ([], [])


guiLen : Int
guiLen =
    let
        (_, ls) =
            parsedGui
    in
        List.length ls


assemble : ClassTable -> ClassTable
assemble (ws, ls1)  =
    let 
        (_, ls2) =
            parsedGui
    in
        (ws, ls2 ++ ls1)


split : ClassTable -> ClassTable
split (ws, clt) =
    (ws, List.drop guiLen clt)