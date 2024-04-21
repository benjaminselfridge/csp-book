module CSPBook where

-- * 1.1

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

-- | Run a process
--
-- Given a list of symbols, run the process for those symbols. Returns @Nothing@
-- if the process is undefined for one of the symbols at any point.
runProcess :: Eq a => Process a -> [a] -> Maybe (Process a)
runProcess p [] = Just p
runProcess (P _ f) (a:as) = case f a of
  Just p' -> runProcess p' as
  Nothing -> Nothing

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
  deriving (Show, Eq)

ex1_1_1 :: Process Vend
ex1_1_1 = Coin .> stop

ex1_1_2 :: Process Vend
ex1_1_2 = Coin .> Choc .> Coin .> Choc .> stop

data Counter = U | R deriving (Show, Eq)
ex1_1_3 :: Process Counter
ex1_1_3 = R .> U .> R .> R .> stop

-- * 1.2

-- | equivalent to Hoare's μX.F(X) notation
μ :: (a -> a) -> a
μ f = let x = f x in x

data Clock = Tick deriving (Show, Eq)

ex1_2_1 :: Process Clock
ex1_2_1 = μ $ \x -> Tick .> x

ex1_2_2 :: Process Vend
ex1_2_2 = μ $ \x -> Coin .> Choc .> x

ex1_2_3 :: Process Vend
ex1_2_3 = μ $ \x -> In5p .> Out2p .> Out1p .> Out2p .> x

ex1_2_4 :: Process Vend
ex1_2_4 = μ $ \x -> In5p .> Out1p .> Out1p .> Out1p .> Out2p .> x

-- * 1.3

choice :: Eq a => [(a, Process a)] -> Process a
choice cs = P (fst <$> cs) (flip lookup cs)

infixr 1 |>
(|>) :: a -> Process a -> (a, Process a)
(|>) = (,)

ex1_3_1 :: Process Counter
ex1_3_1 = choice
  [ U |> stop
  , R |> R .> U .> stop
  ]

ex1_3_2 :: Process Vend
ex1_3_2 = μ $ \x -> In5p .> choice
 [ Out1p |> Out1p .> Out1p .> Out2p .> x
 , Out2p |> Out1p .> Out2p .> x
 ]

ex1_3_3 :: Process Vend
ex1_3_3 = μ $ \x -> Coin .> choice
  [ Choc   |> x
  , Toffee |> x
  ]

-- | WARNING: Do not insert three pennies in a row.
ex1_3_4 :: Process Vend
ex1_3_4 = μ $ \x -> choice
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
