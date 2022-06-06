{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes where

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
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality

-- foundation.contractible-types.is-contr-Π
d_is'45'contr'45'Π_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'Π_16 v0 v1 ~v2 ~v3 v4
  = du_is'45'contr'45'Π_16 v0 v1 v4
du_is'45'contr'45'Π_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'Π_16 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
              (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'is'45'equiv_216
              (coe
                 MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality.d_funext_52 v0
                 v1 erased erased
                 (\ v4 ->
                    coe
                      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
                      (coe v2 v4))
                 v3)
              erased))
-- foundation.contractible-types._.is-contr-equiv-is-contr
d_is'45'contr'45'equiv'45'is'45'contr_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'equiv'45'is'45'contr_50 v0 v1 ~v2 ~v3 v4 v5
  = du_is'45'contr'45'equiv'45'is'45'contr_50 v0 v1 v4 v5
du_is'45'contr'45'equiv'45'is'45'contr_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'equiv'45'is'45'contr_50 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
        -> case coe v3 of
             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v6 v7
               -> coe
                    MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'Σ_384
                    (coe (\ v8 -> v6))
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'prod_312
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'Σ_384
                          (coe (\ v8 -> v4))
                          (coe
                             du_is'45'contr'45'Π_16 (coe v1) (coe v1)
                             (\ v8 ->
                                coe
                                  MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'prop'45'is'45'contr_416)))
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'Σ_384
                          (coe (\ v8 -> v4))
                          (coe
                             du_is'45'contr'45'Π_16 (coe v0) (coe v0)
                             (\ v8 ->
                                coe
                                  MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'prop'45'is'45'contr_416))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.contractible-types._.is-contr-is-contr
d_is'45'contr'45'is'45'contr_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'is'45'contr_84 v0 ~v1 v2
  = du_is'45'contr'45'is'45'contr_84 v0 v2
du_is'45'contr'45'is'45'contr_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'is'45'contr_84 v0 v1
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'Σ_384
             (coe v2)
             (coe
                du_is'45'contr'45'Π_16 (coe v0) (coe v0)
                (\ v4 ->
                   coe
                     MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'prop'45'is'45'contr_416))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.contractible-types._.is-subtype-is-contr
d_is'45'subtype'45'is'45'contr_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'subtype'45'is'45'contr_96 ~v0 ~v1 ~v2
  = du_is'45'subtype'45'is'45'contr_96
du_is'45'subtype'45'is'45'contr_96 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'subtype'45'is'45'contr_96 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'prop'45'is'45'contr_416
-- foundation.contractible-types.is-contr-Prop
d_is'45'contr'45'Prop_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'Prop_108 ~v0 ~v1 = du_is'45'contr'45'Prop_108
du_is'45'contr'45'Prop_108 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'Prop_108
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (\ v0 -> coe du_is'45'subtype'45'is'45'contr_96)
-- foundation.contractible-types._.is-trunc-is-contr
d_is'45'trunc'45'is'45'contr_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'trunc'45'is'45'contr_124 v0 ~v1 v2 v3
  = du_is'45'trunc'45'is'45'contr_124 v0 v2 v3
du_is'45'trunc'45'is'45'contr_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_is'45'trunc'45'is'45'contr_124 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6
        -> coe v2
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8 v3
        -> coe
             MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.d_is'45'trunc'45'succ'45'is'45'trunc_48
             v3 v0 erased
             (coe du_is'45'trunc'45'is'45'contr_124 (coe v0) (coe v3) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.contractible-types._.ev-point
d_ev'45'point_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> AgdaAny
d_ev'45'point_148 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_ev'45'point_148 v3 v5
du_ev'45'point_148 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_ev'45'point_148 v0 v1 = coe v1 v0
-- foundation.contractible-types._.ev-point'
d_ev'45'point''_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny -> () -> (AgdaAny -> AgdaAny) -> AgdaAny
d_ev'45'point''_160 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_ev'45'point''_160 v3 v5
du_ev'45'point''_160 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_ev'45'point''_160 v0 v1 = coe v1 v0
-- foundation.contractible-types._.dependent-universal-property-contr
d_dependent'45'universal'45'property'45'contr_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny -> ()
d_dependent'45'universal'45'property'45'contr_170 = erased
-- foundation.contractible-types._.universal-property-contr
d_universal'45'property'45'contr_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny -> ()
d_universal'45'property'45'contr_182 = erased
-- foundation.contractible-types._.universal-property-dependent-universal-property-contr
d_universal'45'property'45'dependent'45'universal'45'property'45'contr_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'dependent'45'universal'45'property'45'contr_196 ~v0
                                                                           ~v1 ~v2 v3 v4 v5
  = du_universal'45'property'45'dependent'45'universal'45'property'45'contr_196
      v3 v4 v5
du_universal'45'property'45'dependent'45'universal'45'property'45'contr_196 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'dependent'45'universal'45'property'45'contr_196 v0
                                                                            v1 v2
  = coe v0 v1 (\ v3 -> v2)
-- foundation.contractible-types._.is-equiv-ev-point-universal-property-contr
d_is'45'equiv'45'ev'45'point'45'universal'45'property'45'contr_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'ev'45'point'45'universal'45'property'45'contr_212 v0
                                                                   v1 ~v2 v3
  = du_is'45'equiv'45'ev'45'point'45'universal'45'property'45'contr_212
      v0 v1 v3
du_is'45'equiv'45'ev'45'point'45'universal'45'property'45'contr_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'ev'45'point'45'universal'45'property'45'contr_212 v0
                                                                    v1 v2
  = coe v2 v0 v1
-- foundation.contractible-types._.is-contr-is-equiv-ev-point
d_is'45'contr'45'is'45'equiv'45'ev'45'point_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'is'45'equiv'45'ev'45'point_220 ~v0 ~v1 v2 ~v3
  = du_is'45'contr'45'is'45'equiv'45'ev'45'point_220 v2
du_is'45'contr'45'is'45'equiv'45'ev'45'point_220 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'is'45'equiv'45'ev'45'point_220 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe v0) erased
-- foundation.contractible-types._.is-contr-universal-property-contr
d_is'45'contr'45'universal'45'property'45'contr_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'universal'45'property'45'contr_236 ~v0 ~v1 v2 ~v3
  = du_is'45'contr'45'universal'45'property'45'contr_236 v2
du_is'45'contr'45'universal'45'property'45'contr_236 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'universal'45'property'45'contr_236 v0
  = coe du_is'45'contr'45'is'45'equiv'45'ev'45'point_220 (coe v0)
-- foundation.contractible-types._.is-contr-dependent-universal-property-contr
d_is'45'contr'45'dependent'45'universal'45'property'45'contr_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'dependent'45'universal'45'property'45'contr_246 ~v0
                                                                 ~v1 v2 ~v3
  = du_is'45'contr'45'dependent'45'universal'45'property'45'contr_246
      v2
du_is'45'contr'45'dependent'45'universal'45'property'45'contr_246 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'dependent'45'universal'45'property'45'contr_246 v0
  = coe du_is'45'contr'45'universal'45'property'45'contr_236 (coe v0)
-- foundation.contractible-types._.dependent-universal-property-contr-is-contr
d_dependent'45'universal'45'property'45'contr'45'is'45'contr_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'contr'45'is'45'contr_256 ~v0
                                                                 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_dependent'45'universal'45'property'45'contr'45'is'45'contr_256
du_dependent'45'universal'45'property'45'contr'45'is'45'contr_256 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'contr'45'is'45'contr_256
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe (\ v0 v1 -> v0)) erased erased
-- foundation.contractible-types._.universal-property-contr-is-contr
d_universal'45'property'45'contr'45'is'45'contr_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'contr'45'is'45'contr_274 ~v0 ~v1 ~v2 ~v3
                                                    v4
  = du_universal'45'property'45'contr'45'is'45'contr_274 v4
du_universal'45'property'45'contr'45'is'45'contr_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'contr'45'is'45'contr_274 v0
  = coe
      du_universal'45'property'45'dependent'45'universal'45'property'45'contr_196
      (\ v1 v2 ->
         coe
           du_dependent'45'universal'45'property'45'contr'45'is'45'contr_256)
      (coe v0)
-- foundation.contractible-types._.equiv-universal-property-contr
d_equiv'45'universal'45'property'45'contr_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'universal'45'property'45'contr_286 ~v0 ~v1 v2 ~v3 v4 ~v5
  = du_equiv'45'universal'45'property'45'contr_286 v2 v4
du_equiv'45'universal'45'property'45'contr_286 ::
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'universal'45'property'45'contr_286 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_ev'45'point''_160 (coe v0))
      (coe
         du_universal'45'property'45'contr'45'is'45'contr_274 v1 erased)
-- foundation.contractible-types._.is-equiv-self-diagonal-is-equiv-diagonal
d_is'45'equiv'45'self'45'diagonal'45'is'45'equiv'45'diagonal_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'self'45'diagonal'45'is'45'equiv'45'diagonal_308 v0
                                                                 v1 v2
  = coe v2 v0 v1
-- foundation.contractible-types._.is-contr-is-equiv-self-diagonal
d_is'45'contr'45'is'45'equiv'45'self'45'diagonal_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'is'45'equiv'45'self'45'diagonal_314 ~v0 ~v1 v2
  = du_is'45'contr'45'is'45'equiv'45'self'45'diagonal_314 v2
du_is'45'contr'45'is'45'equiv'45'self'45'diagonal_314 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'is'45'equiv'45'self'45'diagonal_314 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_tot_24
      erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
            v0 (\ v1 -> v1)))
-- foundation.contractible-types._.is-contr-is-equiv-diagonal
d_is'45'contr'45'is'45'equiv'45'diagonal_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'is'45'equiv'45'diagonal_326 v0 ~v1 v2
  = du_is'45'contr'45'is'45'equiv'45'diagonal_326 v0 v2
du_is'45'contr'45'is'45'equiv'45'diagonal_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   () ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'is'45'equiv'45'diagonal_326 v0 v1
  = coe
      du_is'45'contr'45'is'45'equiv'45'self'45'diagonal_314
      (coe
         d_is'45'equiv'45'self'45'diagonal'45'is'45'equiv'45'diagonal_308
         (coe v0) erased (coe v1))
-- foundation.contractible-types._.is-equiv-diagonal-is-contr
d_is'45'equiv'45'diagonal'45'is'45'contr_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'diagonal'45'is'45'contr_336 ~v0 ~v1 v2 ~v3 ~v4
  = du_is'45'equiv'45'diagonal'45'is'45'contr_336 v2
du_is'45'equiv'45'diagonal'45'is'45'contr_336 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'diagonal'45'is'45'contr_336 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe
         du_ev'45'point''_160
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
            (coe v0)))
      erased erased
-- foundation.contractible-types._.equiv-diagonal-is-contr
d_equiv'45'diagonal'45'is'45'contr_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'diagonal'45'is'45'contr_352 ~v0 ~v1 ~v2 ~v3 v4
  = du_equiv'45'diagonal'45'is'45'contr_352 v4
du_equiv'45'diagonal'45'is'45'contr_352 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'diagonal'45'is'45'contr_352 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (\ v1 v2 -> v1))
      (coe du_is'45'equiv'45'diagonal'45'is'45'contr_336 (coe v0))
