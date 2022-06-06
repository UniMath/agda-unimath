{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QtruncatedZ45Zmaps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes

-- foundation.truncated-maps._.is-prop-is-trunc-map
d_is'45'prop'45'is'45'trunc'45'map_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'trunc'45'map_20 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_is'45'prop'45'is'45'trunc'45'map_20 v1 v4
du_is'45'prop'45'is'45'trunc'45'map_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'trunc'45'map_20 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.Qpropositions.du_is'45'prop'45'Π_48 v0 ()
      (\ v2 ->
         coe
           MAlonzo.Code.Qfoundation.QtruncatedZ45Ztypes.du_is'45'prop'45'is'45'trunc_240
           (coe ()) (coe v1))
-- foundation.truncated-maps._.is-trunc-map-Prop
d_is'45'trunc'45'map'45'Prop_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'trunc'45'map'45'Prop_30 ~v0 v1 ~v2 ~v3 v4 ~v5
  = du_is'45'trunc'45'map'45'Prop_30 v1 v4
du_is'45'trunc'45'map'45'Prop_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'trunc'45'map'45'Prop_30 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe du_is'45'prop'45'is'45'trunc'45'map_20 (coe v0) (coe v1))
