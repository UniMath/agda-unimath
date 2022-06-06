{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Ztruncation where

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
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs
import qualified MAlonzo.Code.Qfoundation.Qequivalences
import qualified MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality

-- foundation.universal-property-truncation.precomp-Trunc
d_precomp'45'Trunc_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_precomp'45'Trunc_20 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_precomp'45'Trunc_20 v6
du_precomp'45'Trunc_20 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_precomp'45'Trunc_20 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du_precomp_106 (coe v0)
-- foundation.universal-property-truncation.is-truncation
d_is'45'truncation_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> ()
d_is'45'truncation_38 = erased
-- foundation.universal-property-truncation.universal-property-truncation
d_universal'45'property'45'truncation_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> ()
d_universal'45'property'45'truncation_64 = erased
-- foundation.universal-property-truncation.precomp-Π-Truncated-Type
d_precomp'45'Π'45'Truncated'45'Type_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_precomp'45'Π'45'Truncated'45'Type_102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
                                        ~v7 v8 v9
  = du_precomp'45'Π'45'Truncated'45'Type_102 v6 v8 v9
du_precomp'45'Π'45'Truncated'45'Type_102 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_precomp'45'Π'45'Truncated'45'Type_102 v0 v1 v2
  = coe v1 (coe v0 v2)
-- foundation.universal-property-truncation.dependent-universal-property-truncation
d_dependent'45'universal'45'property'45'truncation_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> ()
d_dependent'45'universal'45'property'45'truncation_126 = erased
-- foundation.universal-property-truncation.is-truncation-id
d_is'45'truncation'45'id_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'truncation'45'id_148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_is'45'truncation'45'id_148
du_is'45'truncation'45'id_148 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'truncation'45'id_148
  = coe
      MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'precomp'45'is'45'equiv_360
      (\ v0 -> v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'id_90)
      erased
-- foundation.universal-property-truncation.is-truncation-equiv
d_is'45'truncation'45'equiv_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'truncation'45'equiv_168 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_is'45'truncation'45'equiv_168 v5
du_is'45'truncation'45'equiv_168 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'truncation'45'equiv_168 v0
  = coe
      MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'precomp'45'is'45'equiv_360
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
         (coe v0))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
         (coe v0))
      erased
-- foundation.universal-property-truncation._.is-truncation-universal-property-truncation
d_is'45'truncation'45'universal'45'property'45'truncation_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   (AgdaAny -> AgdaAny) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'truncation'45'universal'45'property'45'truncation_196 v0
                                                              ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_is'45'truncation'45'universal'45'property'45'truncation_196
      v0 v5 v6 v7 v8
du_is'45'truncation'45'universal'45'property'45'truncation_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   (AgdaAny -> AgdaAny) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'truncation'45'universal'45'property'45'truncation_196 v0
                                                               v1 v2 v3 v4
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'equiv'45'is'45'contr'45'map_60
      (coe
         (\ v5 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv_184
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
                 (coe
                    (\ v6 ->
                       coe
                         MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality.du_equiv'45'funext_60
                         (coe v0) (coe v3)
                         (coe
                            MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                            (coe (\ v7 -> v6)) (coe v1))
                         (coe v5))))
              (coe v2 v3 v4 v5)))
-- foundation.universal-property-truncation._.universal-property-truncation-is-truncation
d_universal'45'property'45'truncation'45'is'45'truncation_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'truncation'45'is'45'truncation_212 v0
                                                              ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_universal'45'property'45'truncation'45'is'45'truncation_212
      v0 v5 v6 v7 v8 v9
du_universal'45'property'45'truncation'45'is'45'truncation_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'truncation'45'is'45'truncation_212 v0
                                                               v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v6 ->
               coe
                 MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality.du_equiv'45'funext_60
                 (coe v0) (coe v3)
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                    (coe (\ v7 -> v6)) (coe v1))
                 (coe v5))))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
         (coe v2 v3 v4) v5)
-- foundation.universal-property-truncation._.map-is-truncation
d_map'45'is'45'truncation_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'45'is'45'truncation_232 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_map'45'is'45'truncation_232 v0 v5 v6 v7 v8 v9
du_map'45'is'45'truncation_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'45'is'45'truncation_232 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe
            du_universal'45'property'45'truncation'45'is'45'truncation_212
            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
-- foundation.universal-property-truncation._.triangle-is-truncation
d_triangle'45'is'45'truncation_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'is'45'truncation_250 = erased
-- foundation.universal-property-truncation._.dependent-universal-property-truncation-is-truncation
d_dependent'45'universal'45'property'45'truncation'45'is'45'truncation_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'truncation'45'is'45'truncation_278 ~v0
                                                                           v1 v2 ~v3 v4 v5 v6 ~v7 v8
  = du_dependent'45'universal'45'property'45'truncation'45'is'45'truncation_278
      v1 v2 v4 v5 v6 v8
du_dependent'45'universal'45'property'45'truncation'45'is'45'truncation_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'truncation'45'is'45'truncation_278 v0
                                                                            v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'map'45'Σ_566
      (\ v6 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
           (coe (\ v7 -> v6)) (coe v3))
      (coe v4 v0 v2)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'equiv_736
         (coe
            MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs.du_inv'45'distributive'45'Π'45'Σ_286)
         (coe
            MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs.du_inv'45'distributive'45'Π'45'Σ_286)
         (coe
            v4 ()
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_Σ'45'Truncated'45'Type_350
               (coe v1) (coe v2) (coe v5))))
      (\ v6 -> v6)
-- foundation.universal-property-truncation._.is-truncation-dependent-universal-property-truncation
d_is'45'truncation'45'dependent'45'universal'45'property'45'truncation_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'truncation'45'dependent'45'universal'45'property'45'truncation_306 ~v0
                                                                           ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                                                           v8
  = du_is'45'truncation'45'dependent'45'universal'45'property'45'truncation_306
      v6 v7 v8
du_is'45'truncation'45'dependent'45'universal'45'property'45'truncation_306 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'truncation'45'dependent'45'universal'45'property'45'truncation_306 v0
                                                                            v1 v2
  = coe v0 v1 (\ v3 -> v2)
-- foundation.universal-property-truncation._.sec-is-truncation
d_sec'45'is'45'truncation_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_sec'45'is'45'truncation_324 ~v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 v9 v10
                              ~v11
  = du_sec'45'is'45'truncation_324 v1 v2 v4 v5 v6 v8 v9 v10
du_sec'45'is'45'truncation_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.T_𝕋_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_sec'45'is'45'truncation_324 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs.du_map'45'distributive'45'Π'45'Σ_134
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'is'45'equiv_216
         (coe
            du_dependent'45'universal'45'property'45'truncation'45'is'45'truncation_278
            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.QtruncatedZ45Ztypes.du_fib'45'Truncated'45'Type_376
               (coe v0) (coe v1) (coe v5) (coe v2) (coe v7)))
         (\ v8 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
              (coe v6 v8) erased))
