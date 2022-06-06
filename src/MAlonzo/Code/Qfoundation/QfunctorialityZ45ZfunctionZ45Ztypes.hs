{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QfunctorialityZ45ZfunctionZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes

-- foundation.functoriality-function-types.is-trunc-map-postcomp-is-trunc-map
d_is'45'trunc'45'map'45'postcomp'45'is'45'trunc'45'map_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny
d_is'45'trunc'45'map'45'postcomp'45'is'45'trunc'45'map_20 ~v0 ~v1
                                                          v2 v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_is'45'trunc'45'map'45'postcomp'45'is'45'trunc'45'map_20
      v2 v3 v8
du_is'45'trunc'45'map'45'postcomp'45'is'45'trunc'45'map_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny
du_is'45'trunc'45'map'45'postcomp'45'is'45'trunc'45'map_20 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes.du_is'45'trunc'45'map'45'map'45'Π'45'is'45'trunc'45'map''_346
      (coe v1) (coe v0) erased (coe (\ v3 -> v2))
-- foundation.functoriality-function-types.is-trunc-map-is-trunc-map-postcomp
d_is'45'trunc'45'map'45'is'45'trunc'45'map'45'postcomp_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny
d_is'45'trunc'45'map'45'is'45'trunc'45'map'45'postcomp_50 ~v0 ~v1
                                                          v2 ~v3 ~v4 ~v5 v6
  = du_is'45'trunc'45'map'45'is'45'trunc'45'map'45'postcomp_50 v2 v6
du_is'45'trunc'45'map'45'is'45'trunc'45'map'45'postcomp_50 ::
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_is'45'trunc'45'map'45'is'45'trunc'45'map'45'postcomp_50 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes.du_is'45'trunc'45'map'45'is'45'trunc'45'map'45'map'45'Π''_390
      (coe v0) (coe (\ v2 v3 v4 -> coe v1 v2 v3)) erased
-- foundation.functoriality-function-types.is-equiv-is-equiv-postcomp
d_is'45'equiv'45'is'45'equiv'45'postcomp_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'equiv'45'postcomp_82 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_is'45'equiv'45'is'45'equiv'45'postcomp_82 v5
du_is'45'equiv'45'is'45'equiv'45'postcomp_82 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'equiv'45'postcomp_82 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'equiv'45'is'45'contr'45'map_60
      (coe
         du_is'45'trunc'45'map'45'is'45'trunc'45'map'45'postcomp_50
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6)
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
                 (coe v0 v1 v2))))
-- foundation.functoriality-function-types.is-equiv-is-equiv-postcomp'
d_is'45'equiv'45'is'45'equiv'45'postcomp''_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'equiv'45'postcomp''_106 ~v0 ~v1 v2 ~v3 v4
  = du_is'45'equiv'45'is'45'equiv'45'postcomp''_106 v2 v4
du_is'45'equiv'45'is'45'equiv'45'postcomp''_106 ::
  () ->
  (() ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'equiv'45'postcomp''_106 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
               (coe v1 v0) (\ v2 -> v2))))
      erased erased
-- foundation.functoriality-function-types.is-equiv-postcomp-is-equiv
d_is'45'equiv'45'postcomp'45'is'45'equiv_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'postcomp'45'is'45'equiv_136 ~v0 ~v1 ~v2 ~v3 ~v4 v5
                                             ~v6 ~v7
  = du_is'45'equiv'45'postcomp'45'is'45'equiv_136 v5
du_is'45'equiv'45'postcomp'45'is'45'equiv_136 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'postcomp'45'is'45'equiv_136 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du_postcomp_126
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'is'45'equiv_216
            (coe v0)))
      erased erased
-- foundation.functoriality-function-types.equiv-postcomp
d_equiv'45'postcomp_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'postcomp_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_equiv'45'postcomp_164 v6
du_equiv'45'postcomp_164 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'postcomp_164 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du_postcomp_126
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
            (coe v0)))
      (coe
         du_is'45'equiv'45'postcomp'45'is'45'equiv_136
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
            (coe v0)))
