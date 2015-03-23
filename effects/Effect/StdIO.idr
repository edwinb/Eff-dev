module Effect.StdIO

import Effects
import Control.IOExcept

-------------------------------------------------------------
-- IO effects internals
-------------------------------------------------------------

||| The internal representation of StdIO effects
data StdIO : Effect where
     PutStr : String -> sig StdIO () 
     GetStr : sig StdIO String 
     PutCh : Char -> sig StdIO ()
     GetCh : sig StdIO Char


-------------------------------------------------------------
-- IO effects handlers
-------------------------------------------------------------

instance Handler StdIO IO where
    handle () (PutStr s) k = do putStr s; k () ()
    handle () GetStr     k = do x <- getLine; k x ()
    handle () (PutCh c)  k = do putChar c; k () () 
    handle () GetCh      k = do x <- getChar; k x ()

instance Handler StdIO (IOExcept a) where
    handle () (PutStr s) k = do ioe_lift $ putStr s; k () ()
    handle () GetStr     k = do x <- ioe_lift $ getLine; k x ()
    handle () (PutCh c)  k = do ioe_lift $ putChar c; k () () 
    handle () GetCh      k = do x <- ioe_lift $ getChar; k x ()

-------------------------------------------------------------
--- The Effect and associated functions
-------------------------------------------------------------

STDIO : EFFECT
STDIO = MkEff () StdIO

||| Write a string to standard output.
putStr : String -> Effs () [STDIO]
putStr s = call $ PutStr s

||| Write a character to standard output.
putChar : Char -> Effs () [STDIO]
putChar c = call $ PutCh c

||| Write a string to standard output, terminating with a newline.
putStrLn : String -> Effs () [STDIO]
putStrLn s = putStr (s ++ "\n")

||| Read a string from standard input.
getStr : Effs String [STDIO]
getStr = call $ GetStr

||| Read a character from standard input.
getChar : Effs Char [STDIO]
getChar = call $ GetCh

