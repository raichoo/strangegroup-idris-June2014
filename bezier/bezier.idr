module Bezier

Point : Nat -> Type -> Type
Point = Vect

-- parametric line between two points:
line : Num a => Point d a -> Point d a -> a -> Point d a
line p q t = zipWith interpolate p q
  where
    interpolate a b = (1 - t) * a + t * b

-- bezier of just one point is fixed at that point,
-- and bezier of a list of points is just linear interpolation
-- between bezier of the initial part of the list
-- and bezier of the tail of the list:
bezier : Num a => Vect (1 + n) (Point d a) -> a -> Point d a
bezier [p] t = p
bezier ps t with (ps)
  | (_ :: _ :: _) =
      line (bezier (init ps) t) (bezier (tail ps) t) t
