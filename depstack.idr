module Main

data Expr : Type where
  Val : Int -> Expr
  Add : Expr -> Expr -> Expr

instance Show Expr where
  show (Val value)   = show value
  show (Add lhs rhs) = "(" ++ show lhs ++ " + " ++ show rhs ++ ")"

data Instr : Nat -> Nat -> Type where
  PUSH : Int -> Instr n (1 + n)
  ADD  : Instr (2 + n) (1 + n)

instance Show (Instr m n) where
  show (PUSH value) = "PUSH " ++ show value
  show ADD          = "ADD"

data Sequence : Nat -> Nat -> Type where
  Nil  : Sequence n n
  (::) : Instr m n -> Sequence n o -> Sequence m o

instance Show (Sequence m n) where
  show Nil        = show ""
  show [i]        = show i
  show (i :: is)  = show i ++ "; " ++ show is

total
(++) : Sequence m n -> Sequence n o -> Sequence m o
[]        ++ rest = rest
(i :: is) ++ rest = i :: (is ++ rest)

total
compile : Expr -> Sequence n (1 + n)
compile (Val value)   = [PUSH value]
compile (Add lhs rhs) = compile lhs ++ compile rhs ++ [ADD]

total
run : Sequence m n -> Vect m Int  -> Vect n Int
run Nil stack = stack

run (PUSH value :: is) stack =
  run is (value :: stack)

run (ADD :: is) (lhs :: rhs :: stack) =
  run is ((lhs + rhs) :: stack)

Program : Type
Program = Sequence 0 1

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
