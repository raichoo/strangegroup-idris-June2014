module Main

data Expr : Type where
  Val : Int -> Expr
  Add : Expr -> Expr -> Expr

instance Show Expr where
  show (Val value)   = show value
  show (Add lhs rhs) = "(" ++ show lhs ++ " + " ++ show rhs ++ ")"

data Instr : Type where
  PUSH : Int -> Instr
  ADD  : Instr

instance Show Instr where
  show (PUSH value) = "PUSH " ++ show value
  show ADD          = "ADD"

data Sequence : Type where
  Nil  : Sequence
  (::) : Instr -> Sequence -> Sequence

instance Show Sequence where
  show Nil        = show ""
  show [i]        = show i
  show (i :: is)  = show i ++ "; " ++ show is

total
(++) : Sequence -> Sequence -> Sequence
[]        ++ rest = rest
(i :: is) ++ rest = i :: (is ++ rest)

total
compile : Expr -> Sequence
compile (Val value)   = [PUSH value]
compile (Add lhs rhs) = compile lhs ++ compile rhs ++ [ADD]

partial
run : Sequence -> List Int -> List Int
run Nil stack = stack

run (PUSH value :: is) stack =
  run is (value :: stack)

run (ADD :: is) (lhs :: rhs :: stack) =
  run is ((lhs + rhs) :: stack)

Program : Type
Program = Sequence

main : IO ()
main = do
  prettyPrint "\nExpression" $ show expression
  prettyPrint "Instructions" $ show instrs
  prettyPrint "Result" $ show $ run instrs []
where expression : Expr
      expression = (Add (Add (Val 1) (Val 2)) (Val 3))

      instrs : Program
      instrs = compile expression

      prettyPrint : String -> String -> IO ()
      prettyPrint header body = do
        putStrLn header
        putStrLn "---------------------------------"
        putStrLn $ body ++ "\n"
