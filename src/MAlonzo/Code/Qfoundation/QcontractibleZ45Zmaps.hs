{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QcontractibleZ45Zmaps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QlogicalZ45Zequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QtruncatedZ45Zmaps

-- foundation.contractible-maps._.is-prop-is-contr-map
d_is'45'prop'45'is'45'contr'45'map_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'is'45'contr'45'map_18 ~v0 v1 ~v2 ~v3 ~v4
  = du_is'45'prop'45'is'45'contr'45'map_18 v1
du_is'45'prop'45'is'45'contr'45'map_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'is'45'contr'45'map_18 v0
  = coe
      MAlonzo.Code.Qfoundation.QtruncatedZ45Zmaps.du_is'45'prop'45'is'45'trunc'45'map_20
      (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6)
-- foundation.contractible-maps._.is-contr-map-Prop
d_is'45'contr'45'map'45'Prop_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'map'45'Prop_22 ~v0 v1 ~v2 ~v3 ~v4
  = du_is'45'contr'45'map'45'Prop_22 v1
du_is'45'contr'45'map'45'Prop_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'map'45'Prop_22 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe du_is'45'prop'45'is'45'contr'45'map_18 (coe v0))
-- foundation.contractible-maps._.equiv-is-equiv-is-contr-map
d_equiv'45'is'45'equiv'45'is'45'contr'45'map_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'is'45'equiv'45'is'45'contr'45'map_42 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_equiv'45'is'45'equiv'45'is'45'contr'45'map_42
du_equiv'45'is'45'equiv'45'is'45'contr'45'map_42 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'is'45'equiv'45'is'45'contr'45'map_42
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QlogicalZ45Zequivalences.du_equiv'45'iff_72
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'equiv'45'is'45'contr'45'map_60)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128)
-- foundation.contractible-maps._.equiv-is-contr-map-is-equiv
d_equiv'45'is'45'contr'45'map'45'is'45'equiv_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'is'45'contr'45'map'45'is'45'equiv_48 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_equiv'45'is'45'contr'45'map'45'is'45'equiv_48
du_equiv'45'is'45'contr'45'map'45'is'45'equiv_48 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'is'45'contr'45'map'45'is'45'equiv_48
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QlogicalZ45Zequivalences.du_equiv'45'iff_72
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'equiv'45'is'45'contr'45'map_60)
