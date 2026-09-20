module CoverageCheck.Data.List.Some.Core where

import CoverageCheck.Data.List.Many.Core (Many(MHere, MThere))

data Some p = SHere p (Many p)
            | SThere (Some p)
                deriving (Eq, Show)

someToMany :: Some p -> Many p
someToMany (SHere px pxs) = MHere px pxs
someToMany (SThere pxs) = MThere (someToMany pxs)

tailSome :: Some p -> Many p
tailSome (SHere px pxs) = pxs
tailSome (SThere pxs) = someToMany pxs

unthereSome :: Some p -> Some p
unthereSome (SHere px pxs) = undefined
unthereSome (SThere pxs) = pxs

