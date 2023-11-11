open import Data.String
open import Data.Product

Writer : Set → Set
Writer a = ( a × String )
