module IdInfo where
import GhcPrelude
import Outputable
data IdInfo
data IdDetails

vanillaIdInfo :: IdInfo
coVarDetails :: IdDetails
isCoVarDetails :: IdDetails -> Bool
isCoercionHoleDetails :: IdDetails -> Bool
pprIdDetails :: IdDetails -> SDoc

