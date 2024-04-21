{-# LANGUAGE MultiWayIf #-}

module CSPBook where

import Control.Monad (foldM)
import Data.Functor ((<&>))
import Data.List (transpose, union, intersect, (\\))
import Data.Maybe (isJust, mapMaybe)

import Prelude hiding ((||))

-- * 1.1.1

-- | Process
--
-- Note that the list field is just a list of valid prefixes; it is not actually
-- used, except to recover those prefixes. Every valid process should return a
-- @Just@ value for exactly those elements in the prefix list, and @Nothing@ for
-- values not in the list. The list must be finite.
data Process a = P [a] (a -> Maybe (Process a))

prefixes :: Process a -> [a]
prefixes (P pfxs _) = pfxs

stop :: Process a
stop = P [] (\x -> Nothing)

-- | Prefix operator
--
-- This produces a process that starts with a particular prefix, then continues
-- as another process.
infixr 1 .>
(.>) :: Eq a => a -> Process a -> Process a
a .> p = P [a] (\x -> if x == a then Just p else Nothing)

data Vend = Coin
          | Choc
          | Toffee
          | In5p
          | In2p
          | In1p
          | Out2p
          | Out1p
          | Large
          | Small
          | SetOrange
          | SetLemon
          | Orange
          | Lemon
          | Clink
          | Clunk
          | Curse
  deriving (Show, Eq)

ex1_1_1_1 :: Process Vend
ex1_1_1_1 = Coin .> stop

ex1_1_1_2 :: Process Vend
ex1_1_1_2 = Coin .> Choc .> Coin .> Choc .> stop

data Direction = U | D | R | A -- A is "around"
  deriving (Show, Eq)
ex1_1_1_3 :: Process Direction
ex1_1_1_3 = R .> U .> R .> R .> stop

-- * 1.2

-- | equivalent to Hoare's μX.F(X) notation
μ :: (a -> a) -> a
μ f = let x = f x in x

data Clock = Tick deriving (Show, Eq)

ex1_1_2_1 :: Process Clock
ex1_1_2_1 = μ $ \x -> Tick .> x

ex1_1_2_2 :: Process Vend
ex1_1_2_2 = μ $ \x -> Coin .> Choc .> x

ex1_1_2_3 :: Process Vend
ex1_1_2_3 = μ $ \x -> In5p .> Out2p .> Out1p .> Out2p .> x

ex1_1_2_4 :: Process Vend
ex1_1_2_4 = μ $ \x -> In5p .> Out1p .> Out1p .> Out1p .> Out2p .> x

-- * 1.3

choice :: Eq a => [(a, Process a)] -> Process a
choice cs = P (fst <$> cs) (flip lookup cs)

infixr 1 |>
(|>) :: a -> Process a -> (a, Process a)
(|>) = (,)

ex1_1_3_1 :: Process Direction
ex1_1_3_1 = choice
  [ U |> stop
  , R |> R .> U .> stop
  ]

ex1_1_3_2 :: Process Vend
ex1_1_3_2 = μ $ \x -> In5p .> choice
 [ Out1p |> Out1p .> Out1p .> Out2p .> x
 , Out2p |> Out1p .> Out2p .> x
 ]

ex1_1_3_3 :: Process Vend
ex1_1_3_3 = μ $ \x -> Coin .> choice
  [ Choc   |> x
  , Toffee |> x
  ]

-- | WARNING: Do not insert three pennies in a row.
ex1_1_3_4 :: Process Vend
ex1_1_3_4 = μ $ \x -> choice
  [ In2p |> choice
    [ Large |> x
    , Small |> Out1p .> x
    ]
  , In1p |> choice
    [ Small |> x
    , In1p |> choice
      [ Large |> x
      , In1p |> stop
      ]
    ]
  ]

ex1_1_3_5 :: Process Vend
ex1_1_3_5 = μ $ \x -> choice
  [ Coin |> Choc .> x
  , Choc |> Coin .> x
  ]

ex1_1_3_6 :: Process Vend
ex1_1_3_6 = μ $ \x -> Coin .> ex1_1_3_5

data Copy = In0 | In1 | Out0 | Out1 deriving (Show, Eq)

ex1_1_3_7 :: Process Copy
ex1_1_3_7 = μ $ \x -> choice
  [ In0 |> Out0 .> x
  , In1 |> Out1 .> x
  ]

-- * 1.1.4

-- | Mutually-recursive fixed-point operator
μs :: [ [a] -> a ] -> [a]
μs fl = μ (\x -> map ($ x) fl)

ex1_1_4_1 :: Process Vend
ex1_1_4_1 =
  let [dd, g, w] = μs $
        [ \[dd, g, w] -> choice [ SetOrange |> g, SetLemon |> w]
        , \[dd, g, w] -> choice [ Coin |> Orange .> g, SetLemon  |> w ]
        , \[dd, g, w] -> choice [ Coin |> Lemon  .> w, SetOrange |> g ]
        ]
  in dd

ex1_1_4_2 :: Process Direction
ex1_1_4_2 =
  let cts = μs $
        ( \x -> choice [ U |> x !! 1 , A |> x !! 0 ] ) :
        ( [1..] <&> \i ->
            \x -> choice [ U |> x !! (i+1), D |> x !! (i-1)] )
  in cts !! 0

-- * 1.8

-- | Fair n-way interleaving. Stole this from dmwit's universe package.
interleave :: [[a]] -> [a]
interleave = concat . transpose

-- | Get all the traces of a process fairly.
traces :: Process a -> [[a]]
traces (P [] _) = [[]]
traces (P pfxs f) = [[]] ++ interleave (g `mapMaybe` pfxs)

  where g a = case f a of
          Nothing -> Nothing
          Just p -> Just ((a:) <$> traces p)

-- | Run a process on a single input to get (possibly) a new process
applyProcess :: Eq a => Process a -> a -> Maybe (Process a)
applyProcess (P _ f) a = f a

-- | Run a process
--
-- Given a list of symbols, run the process for those symbols. Returns @Nothing@
-- if the process is undefined for one of the symbols at any point.
runProcess :: Eq a => Process a -> [a] -> Maybe (Process a)
runProcess = foldM applyProcess

-- | Run a process and determine whether the run was valid
isTrace :: Eq a => Process a -> [a] -> Bool
isTrace p as = isJust (runProcess p as)

-- * 2

-- | Process tagged with its own alphabet.
data AProcess a = AP [a] (Process a)

(||) :: Eq a => AProcess a -> AProcess a -> AProcess a
ap1 || ap2 =
  let AP alph1 p1 = ap1
      AP alph2 p2 = ap2

      commonAlph = alph1 `intersect` alph2
      alph1' = alph1 \\ alph2 -- p1's exclusive alphabet
      alph2' = alph2 \\ alph1 -- p2's exclusive alphabet

      p = go alph1' alph2' commonAlph p1 p2

  in AP (alph1' ++ alph2' ++ commonAlph) p

  where go alph1' alph2' commonAlph p1 p2 =
          let pfxs1' = prefixes p1 `intersect` alph1'
              pfxs2' = prefixes p2 `intersect` alph2'
              commonPfxs = commonAlph `intersect` prefixes p1 `intersect` prefixes p2

              P _ f1 = p1
              P _ f2 = p2

              f a = if | a `elem` pfxs1' ->
                         go alph1' alph2' commonAlph <$> f1 a <*> pure p2
                       | a `elem` pfxs2' ->
                         go alph1' alph2' commonAlph <$> pure p1 <*> f2 a
                       | a `elem` commonPfxs ->
                         go alph1' alph2' commonAlph <$> f1 a <*> f2 a
                       | otherwise -> Nothing

          in P (pfxs1' ++ pfxs2' ++ commonPfxs) f

ex2_2_1 :: Process Vend
ex2_2_1 = let AP _ p = AP [Toffee, Choc, Coin] grCust ||
                       AP [Toffee, Choc, Coin] vmct
          in p
  where grCust = choice
          [ Toffee |> grCust
          , Choc |> grCust
          , Coin |> Choc .> grCust
          ]
        vmct = Coin .> choice
          [ Choc   |> vmct
          , Toffee |> vmct
          ]

ex2_2_2 :: Process Vend
ex2_2_2 = let AP _ p = AP [In1p, In2p, Large] foolCust ||
                       AP [In1p, In2p, Large, Small, Out1p] vmc
          in p
  where foolCust = choice
          [ In2p |> Large .> foolCust
          , In1p |> Large .> foolCust
          ]
        vmc = choice
          [ In2p |> choice [ Large |> vmc
                           , Small |> Out1p .> vmc
                           ]
          , In1p |> choice [ Small|> vmc
                           , In1p |> choice [ Large |> vmc
                                            , In1p |> stop
                                            ]
                           ]
          ]

ex2_3_1 :: Process Vend
ex2_3_1 = let AP _ p = noisyVM || cust
          in p
  where noisyVM = AP [Coin, Choc, Clink, Clunk, Toffee] $
          μ $ \x -> Coin .> Clink .> Choc .> Clunk .> x
        cust = AP [Coin, Choc, Curse, Toffee] $
          μ $ \x -> Coin .> choice
                    [ Toffee |> x
                    , Curse |> Choc .> x
                    ]
