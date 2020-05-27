# idris-data-frame

This is a library for [Idris 2](https://github.com/edwinb/Idris2/),
trying to replicate the feel of R's
[tidyverse](https://www.tidyverse.org/)/[dplyr](https://dplyr.tidyverse.org/).

Here's how you make data frame literals:
```idris
import DataFrame

df : DF ["name" :- String, "age" :- Int, "pet" :- Maybe String]
df = MkDF
  [ ["Joe", "Anne", "Lisa", "Bob", "Zorg"]
  , [11, 22, 22, 33, 22]
  , [Just "fish", Nothing, Just "dog", Just "cat", Just "mech"]
  ]
```

Here's how you read them from a CSV file:
```idris
Right people <- readCsv "/home/ziman/dev/dframe/example.csv"
  [ "name"      :- String
  , "age"       :- Int
  , "gender"    :- Maybe String
  , "pet"       :- Maybe String
  ]
  Left err => putStrLn err

printLn people
```
```
name     age gender pet   
-------- --- ------ ------
Anne      12 F            
Joe       23 M      dog   
Alistair  34 M            
Dee       45        dog   
Morag     56 F      dog   
Callum    67 M      cat   
Hamish    78 M      futret
```

[dplyr](https://dplyr.tidyverse.org/)-style manipulation:
```idris
people
  ~> modify
      [ "male_with_pet" :-
          (col "gender" == val (Just "M"))
            && (isJust <$> col "pet")
      ]
  ~> orderBy [Asc "male_with_pet", Asc "age"]
  ~> printLn
```
```
name     age gender pet    male_with_pet
-------- --- ------ ------ -------------
Anne      12 F             no           
Alistair  34 M             no           
Dee       45        dog    no           
Morag     56 F      dog    no           
Joe       23 M      dog    yes          
Callum    67 M      cat    yes          
Hamish    78 M      futret yes          
```

Expressions are applicative functors and have instances
of `Num`, `Neg`, `Fractional`, `Integral`, etc. as long as
the underlying types do, to reduce syntactic noise.

Aggregation and grouping:
```idris
people
  ~> groupBy ["pet"]
  ~> summarise ["count" :- count {a=Int}]
  ~> modify ["pet" :- fromMaybe "(no pet)" <$> col "pet"]
  ~> orderBy [Desc (col "count")]
  ~> printLn
```
```
pet      count
-------- -----
dog          3
(no pet)     2
futret       1
cat          1
```

Some more manipulation:
```idris
people
  ~> where_ (isJust <$> col "pet")
  ~> select
      [ "name" :- col "name"
      , "age" :- col "age"
      , "half_age_plus7" :- (col "age" `div` 2 + 7)
      , "age_minus7_dbl" :- ((col "age" - 7) * 2)
      ]
  ~> orderBy [Asc "age"]
  ~> printLn
```
```
name   age half_age_plus7 age_minus7_dbl
------ --- -------------- --------------
Joe     23             18             32
Dee     45             29             76
Morag   56             35             98
Callum  67             40            120
Hamish  78             46            142
```
