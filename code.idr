module Main

%default total

hasPred : (n : Nat) -> Either (n = Z) (m : Nat ** n = (S m))
hasPred Z     = Left refl
hasPred (S k) = Right (k ** refl)

data MyNat : Type where
  Z : MyNat
  S : MyNat -> MyNat

%name MyNat m,n,o

myPlus : MyNat -> MyNat -> MyNat
myPlus Z n     = n
myPlus (S m) n = S (myPlus m n)

plus0 : (n : MyNat) -> myPlus Z n = myPlus n Z
plus0 Z     = refl
plus0 (S m) = let ih = plus0 m in
                  rewrite ih in refl

plusS : (n, m : MyNat) -> myPlus n (S m) = S (myPlus n m)
plusS Z m     = refl
plusS (S n) m = let ih = plusS n m in
                    rewrite ih in refl

plusComm : (n, m : MyNat) -> myPlus n m = myPlus m n
plusComm Z m     = let ih = plus0 m in
                       rewrite ih in refl
plusComm (S n) m = let ih = plusS m n in
                       rewrite ih in
                               let ih' = plusComm n m in
                                   rewrite ih' in
                                           refl

data HList : Vect n Type -> Type where
  Nil  : HList []
  (::) : {ts : Vect n Type} -> (a : t) -> (as : HList ts) -> HList (t :: ts)

hlistTest : HList [Bool, String, Nat]
hlistTest = [True, "foo", 0]

append : {ts1 : Vect n Type} ->
         {ts2 : Vect m Type} ->
         (xs : HList ts1)    ->
         (ys : HList ts2)    ->
         HList (ts1 ++ ts2)
append []        ys = ys
append (a :: as) ys = a :: append as ys

lookup : (i : Fin n) -> HList ts -> index i ts
lookup fZ     (a :: as) = a
lookup (fS y) (a :: as) = lookup y as

depBoolElim : (C : Bool -> Type) ->
              (c : Bool) -> (t : C True) -> (f : C False) -> C c
depBoolElim C False t f = f
depBoolElim C True t f  = t

syntax if [cond] return [C] then [t] else [f] = depBoolElim C cond t f

ifTest : Nat
ifTest = if True return C then 0 else "foo"
  where
    C : Bool -> Type
    C True  = Nat
    C False = String

data TreeShape : Type where
  LeafShape   : TreeShape
  BranchShape : TreeShape -> TreeShape -> TreeShape

namespace Tree
  data Tree : TreeShape -> Type -> Type where
    Leaf : a -> Tree LeafShape a
    Branch : (left : Tree s a)   ->
             (value : a)         ->
             (right : Tree s' a) ->
             Tree (BranchShape s s') a

  zipTree : Tree s a -> Tree s b -> Tree s (a, b)
  zipTree (Leaf x) (Leaf y) = Leaf (x, y)
  zipTree (Branch l v r) (Branch l' v' r') =
    Branch (zipTree l l') (v, v') (zipTree r r')

data Image : (a -> b) -> b -> Type where
  Im : {f : a -> b} -> (x : a) -> Image f (f x)

inv : (f : a -> b) -> (y : b) -> Image f y -> a
inv f (f x) (Im x) = x

data BinTree : Type -> Type where
  Leaf   : (value : a) -> BinTree a
  Branch : (left : BinTree a) -> (right : BinTree a) -> BinTree a

using (x : a, l : BinTree a, r : BinTree a)
  data IsElem : a -> BinTree a -> Type where
    Here    : IsElem x (Leaf x)
    IsLeft  : IsElem x l -> IsElem x (Branch l r)
    IsRight : IsElem x r -> IsElem x (Branch l r)

foundInLeaf : {x, y : a} -> IsElem x (Leaf y) -> x = y
foundInLeaf Here = refl

foundInTree : {x : a}                      ->
              {left, right : BinTree a}    ->
              IsElem x (Branch left right) ->
              Either (IsElem x left) (IsElem x right)
foundInTree (IsLeft x)  = Left x
foundInTree (IsRight x) = Right x

isElem : DecEq a => (x : a) -> (t : BinTree a) -> Dec (IsElem x t)
isElem x (Leaf value) with (decEq x value)
  isElem x (Leaf x)     | Yes refl = Yes Here
  isElem x (Leaf value) | No nc    = No $ \p => nc (foundInLeaf p)
isElem x (Branch left right) with (isElem x left)
  isElem x (Branch left right) | Yes prf = Yes (IsLeft prf)
  isElem x (Branch left right) | No nl with (isElem x right)
    isElem x (Branch left right) | No nl | Yes prf = Yes (IsRight prf)
    isElem x (Branch left right) | No nl | No nr   =
      No $ \p => case foundInTree p of
                      Left x  => nl x
                      Right x => nr x

concatAssoc : (x, y, z : List a) -> (x ++ y) ++ z = x ++ y ++ z
concatAssoc []        y z = refl
concatAssoc (x :: xs) y z = rewrite concatAssoc xs y z in refl

listRightNeutral : (l : List a) -> l ++ [] = l
listRightNeutral []        = refl
listRightNeutral (x :: xs) = rewrite listRightNeutral xs in refl

instance VerifiedSemigroup (List a) where
  semigroupOpIsAssociative []        c r = refl
  semigroupOpIsAssociative (x :: xs) c r =
    rewrite concatAssoc xs c r in refl

instance VerifiedMonoid (List a) where
  monoidNeutralIsNeutralL l = rewrite listRightNeutral l in refl
  monoidNeutralIsNeutralR l = refl
