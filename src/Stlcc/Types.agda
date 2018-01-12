module Stlcc.Types where

infix 7 _⇒_

data Type : Set where
  𝟘 𝟙         : Type
  _⇒_ _×_ _+_ : Type → Type → Type
