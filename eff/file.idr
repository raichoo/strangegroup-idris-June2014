module Main

import Effects
import Effect.File
import Effect.StdIO

import Lightyear.Core
import Lightyear.Combinators
import Lightyear.Strings

import Json

readJSON : String -> { [FILE_IO (), STDIO] } Eff IO (Maybe JsonValue)
readJSON f = do
  case !(open f Read) of
       True => do l <- readLine
                  close -- you have to close the file, otherwise: compile error
                  case parse jsonToplevelValue l of
                       Left e   => do
                         putStrLn e
                         return Nothing
                       Right x  => return $ Just x
       False => do
         -- close will yield a compile error here, you cannot close a file that
         -- is not open.
         return Nothing

main : IO ()
main = do
  Just (JsonObject j) <- run $ readJSON "test.txt"
                                 | Nothing => putStrLn "No JSON parsed"
  print (lookup "foo" j)
