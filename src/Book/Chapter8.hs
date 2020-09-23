{-@ LIQUID "--no-termination" @-}

module Book.Chapter8 where

import Data.Set hiding (insert, partition, filter, split, elems)
import Prelude  hiding (elem, reverse, filter)

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

{-@ type True  = {v:Bool |     v} @-}
{-@ type False = {v:Bool | not v} @-}

{-@ type Implies P Q = {v:_ | v <=> (P => Q)} @-}

{-@ implies        :: p:Bool -> q:Bool -> Implies p q  @-}
implies :: Bool -> Bool -> Bool
implies False _    = True
implies _     True = True
implies _    _     = False

{-@ prop_one_plus_one_eq_two :: _ -> True @-}
prop_one_plus_one_eq_two x = (x == 1 + 1) `implies` (x == 2)

-- Exercise

{-@ prop_x_y_200 :: _ -> _ -> True @-}
prop_x_y_200 x y = ((x < 100) && (y < 100))
                    `implies` (x + y < 200)

--

{-@ prop_intersection_comm :: _ -> _ -> True @-}
prop_intersection_comm x y
  = (x `intersection` y) == (y `intersection` x)

{-@ prop_union_assoc :: _ -> _ -> _ -> True @-}
prop_union_assoc x y z
  = (x `union` (y `union` z)) == (x `union` y) `union` z

{-@ prop_intersection_dist :: _ -> _ -> _ -> True @-}
prop_intersection_dist x y z
  =  x `intersection` (y `union` z)
     ==
     (x `intersection` y) `union` (x `intersection` z)

-- Exercise

-- It fails if elements of x are in y (because then the difference
-- removes them) => We need x and y to be disjoint.

{-@ fail prop_cup_dif_bad @-}
{-@ prop_cup_dif_bad :: _ -> _ -> True @-}
prop_cup_dif_bad x y
  = pre `implies` (x == ((x `union` y) `difference` y))
  where
    pre = True  -- Fix this with a non-trivial precondition

{-@ prop_cup_dif_bad' :: _ -> _ -> True @-}
prop_cup_dif_bad' x y
  = pre `implies` (x == ((x `union` y) `difference` y))
  where
    pre = (x `intersection` y == empty)

--

{-@ measure elts @-}
elts :: (Ord a) => [a] -> Set a
elts []     = empty
elts (x:xs) = singleton x `union` elts xs

-- A list with elements S
{-@ type ListS a S = {v:[a] | elts v = S} @-}
-- An empty list
{-@ type ListEmp a = ListS a {Set_empty 0} @-}
-- A list whose contents equal those of list X
{-@ type ListEq a X = ListS a {elts X}    @-}
-- A list whose contents are a subset of list X
{-@ type ListSub a X = {v:[a]| Set_sub (elts v) (elts X)} @-}
-- A list whose contents are the union of lists X and Y
{-@ type ListUn a X Y = ListS a {Set_cup (elts X) (elts Y)} @-}
-- A list whose contents are exactly X and the contents of Y
{-@ type ListUn1 a X Y = ListS a {Set_cup (Set_sng X) (elts Y)} @-}

