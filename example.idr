module Main

import Data.Maybe
import DataFrame

df : DF
  [ "name" :- String
  , "age"  :- Int
  , "pet"  :- Maybe String
  ]
df = MkDF
  [ ["Joe", "Anne", "Lisa", "Bob", "Zorg"]
  , [11, 22, 22, 33, 22]
  , [Just "fish", Nothing, Just "dog", Just "cat", Just "mech"]
  ]

main : IO ()
main = do
  Right people <- readCsv "example.csv"
    [ "name"      :- String
    , "age"       :- Int
    , "gender"    :- Maybe String
    , "pet"       :- Maybe String
    ]
    | Left err => putStrLn $ "could not load example.csv: " ++ err

  printLn people
  printLn (people ^. "name")

  people
    ~> modify
        [ "male_with_pet" :-
            (col "gender" == val (Just "M"))
              && (isJust <$> col "pet")
        ]
    ~> orderBy [Asc (col "male_with_pet"), Asc (col "age")]
    ~> printLn

  people
    ~> where_ (isJust <$> col "pet")
    ~> select
        [ "name" :- col "name"
        , "age" :- col "age"
        , "half_age_plus7" :- (col "age" `div` 2 + 7)
        , "age_minus7_dbl" :- ((col "age" - 7) * 2)
        ]
    ~> orderBy [Asc (col "age")]
    ~> printLn

  people
    ~> groupBy ["pet"]
    ~> summarise ["count" :- count {a=Int}]
    ~> modify ["pet" :- fromMaybe "(no pet)" <$> col "pet"]
    ~> orderBy [Desc (col "count")]
    ~> printLn
