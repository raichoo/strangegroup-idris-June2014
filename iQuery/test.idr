module Main

import IQuery

fac : Integer -> Integer
fac n = product [1..n]

main : IO ()
main = do
  nodes  <- query "#test"
  Just e <- nodes `elemAt` 0
              | Nothing => alert "Nothing to see here"

  print !(getText e)
  e `setText` "foo"
  e `onClick` (\event => do setText e "clicked"
                            alert (show $ fac 1000)
                            return 1)
  print !(getText e)
