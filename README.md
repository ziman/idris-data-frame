# idris-data-frame

Let's get imports out of the way first.
```idris
module Main

import Data.Maybe
import DataFrame
```

Here's how you make data frame literals:
```idris
df : DF ["name" :- String, "age" :- Int, "pet" :- Maybe String]
df = MkDF
  [ ["Joe", "Anne", "Lisa", "Bob", "Zorg"]
  , [11, 22, 22, 33, 22]
  , [Just "fish", Nothing, Just "dog", Just "cat", Just "mech"]
  ]
```

Here's how you read them from a CSV file:
```idris
Right pets <- readCsv "/home/ziman/dev/dframe/example.csv"
  [ "name"      :- String
  , "age"       :- Int
  , "gender"    :- Maybe String
  , "pet"       :- Maybe String
  ]

printLn pets
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
pets
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

Some more manipulation:
```idris
pets
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
