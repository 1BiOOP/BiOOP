module OOP.Printer.String exposing (..)

import String
import OOP.Syntax exposing (..)

printString : Term -> String
printString t =
    case t of
        TEmpStr _ ->
            ""
        
        TString _ (TChar _ c) t2 -> 
            (String.fromChar c) ++ (printString t2)

        _ ->
            "Print String Error : 01."

printPatternString : Pattern -> String
printPatternString p =
    case p of
        PEmpStr _ ->
            ""

        PString _ (PChar _ c) p2 ->
            (String.fromChar c) ++ (printPatternString p2)

        _ ->
            "print Pattern String Error : 01."