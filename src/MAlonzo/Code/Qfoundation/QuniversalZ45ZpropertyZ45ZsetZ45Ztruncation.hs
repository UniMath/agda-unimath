{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation where

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
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs
import qualified MAlonzo.Code.Qfoundation.Qequivalences
import qualified MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality
import qualified MAlonzo.Code.Qfoundation.QreflectingZ45ZmapsZ45ZequivalenceZ45Zrelations
import qualified MAlonzo.Code.Qfoundation.Qsets

-- foundation.universal-property-set-truncation.is-set-truncation
d_is'45'set'45'truncation_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> ()
d_is'45'set'45'truncation_14 = erased
-- foundation.universal-property-set-truncation.universal-property-set-truncation
d_universal'45'property'45'set'45'truncation_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> ()
d_universal'45'property'45'set'45'truncation_36 = erased
-- foundation.universal-property-set-truncation.precomp-Π-Set
d_precomp'45'Π'45'Set_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_precomp'45'Π'45'Set_70 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8
  = du_precomp'45'Π'45'Set_70 v5 v7 v8
du_precomp'45'Π'45'Set_70 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_precomp'45'Π'45'Set_70 v0 v1 v2 = coe v1 (coe v0 v2)
-- foundation.universal-property-set-truncation.dependent-universal-property-set-truncation
d_dependent'45'universal'45'property'45'set'45'truncation_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> ()
d_dependent'45'universal'45'property'45'set'45'truncation_92
  = erased
-- foundation.universal-property-set-truncation.is-set-truncation-universal-property
d_is'45'set'45'truncation'45'universal'45'property_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   (AgdaAny -> AgdaAny) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'truncation'45'universal'45'property_114 v0 v1 ~v2
                                                       ~v3 ~v4 v5 v6 v7
  = du_is'45'set'45'truncation'45'universal'45'property_114
      v0 v1 v5 v6 v7
du_is'45'set'45'truncation'45'universal'45'property_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   (AgdaAny -> AgdaAny) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'truncation'45'universal'45'property_114 v0 v1 v2 v3
                                                        v4
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
                         (coe v1) (coe v0)
                         (coe
                            MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                            (coe (\ v7 -> v6)) (coe v2))
                         (coe v5))))
              (coe v3 v4 v5)))
-- foundation.universal-property-set-truncation.universal-property-is-set-truncation
d_universal'45'property'45'is'45'set'45'truncation_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'is'45'set'45'truncation_144 v0 v1 ~v2
                                                       ~v3 ~v4 v5 v6 v7 v8
  = du_universal'45'property'45'is'45'set'45'truncation_144
      v0 v1 v5 v6 v7 v8
du_universal'45'property'45'is'45'set'45'truncation_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'is'45'set'45'truncation_144 v0 v1 v2 v3
                                                        v4 v5
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'tot_340
         (coe
            (\ v6 ->
               coe
                 MAlonzo.Code.Qfoundation.QfunctionZ45Zextensionality.du_equiv'45'funext_60
                 (coe v1) (coe v0)
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
                    (coe (\ v7 -> v6)) (coe v2))
                 (coe v5))))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'contr'45'map'45'is'45'equiv_128
         (coe v3 v4) v5)
-- foundation.universal-property-set-truncation.map-is-set-truncation
d_map'45'is'45'set'45'truncation_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'45'is'45'set'45'truncation_180 v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8
  = du_map'45'is'45'set'45'truncation_180 v0 v2 v5 v6 v7 v8
du_map'45'is'45'set'45'truncation_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'45'is'45'set'45'truncation_180 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe
            du_universal'45'property'45'is'45'set'45'truncation_144 (coe v1)
            (coe v0) (coe v2) (coe v3 v1) (coe v4) (coe v5)))
-- foundation.universal-property-set-truncation.triangle-is-set-truncation
d_triangle'45'is'45'set'45'truncation_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'is'45'set'45'truncation_212 = erased
-- foundation.universal-property-set-truncation.is-set-truncation-id
d_is'45'set'45'truncation'45'id_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'truncation'45'id_232 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_is'45'set'45'truncation'45'id_232
du_is'45'set'45'truncation'45'id_232 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'truncation'45'id_232
  = coe
      MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'precomp'45'is'45'equiv_360
      (\ v0 -> v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'id_90)
      erased
-- foundation.universal-property-set-truncation.is-set-truncation-equiv
d_is'45'set'45'truncation'45'equiv_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'truncation'45'equiv_250 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_is'45'set'45'truncation'45'equiv_250 v4
du_is'45'set'45'truncation'45'equiv_250 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'truncation'45'equiv_250 v0
  = coe
      MAlonzo.Code.Qfoundation.Qequivalences.du_is'45'equiv'45'precomp'45'is'45'equiv_360
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
         (coe v0))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'map'45'equiv_52
         (coe v0))
      erased
-- foundation.universal-property-set-truncation.dependent-universal-property-is-set-truncation
d_dependent'45'universal'45'property'45'is'45'set'45'truncation_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'is'45'set'45'truncation_272 ~v0
                                                                    v1 ~v2 ~v3 v4 v5 v6 v7
  = du_dependent'45'universal'45'property'45'is'45'set'45'truncation_272
      v1 v4 v5 v6 v7
du_dependent'45'universal'45'property'45'is'45'set'45'truncation_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'is'45'set'45'truncation_272 v0
                                                                     v1 v2 v3 v4
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_is'45'fiberwise'45'equiv'45'is'45'equiv'45'map'45'Σ_566
      (\ v5 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
           (coe (\ v6 -> v5)) (coe v2))
      (coe v3 v0 v1)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'equiv_736
         (coe
            MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs.du_inv'45'distributive'45'Π'45'Σ_286)
         (coe
            MAlonzo.Code.Qfoundation.QdistributivityZ45ZofZ45ZdependentZ45ZfunctionsZ45ZoverZ45ZdependentZ45Zpairs.du_inv'45'distributive'45'Π'45'Σ_286)
         (coe
            v3 ()
            (coe
               MAlonzo.Code.Qfoundation.Qsets.du_Σ'45'Set_30 (coe v1) (coe v4))))
      (\ v5 -> v5)
-- foundation.universal-property-set-truncation.is-set-truncation-dependent-universal-property
d_is'45'set'45'truncation'45'dependent'45'universal'45'property_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'truncation'45'dependent'45'universal'45'property_316 ~v0
                                                                    ~v1 v2 ~v3 ~v4 ~v5 v6 v7
  = du_is'45'set'45'truncation'45'dependent'45'universal'45'property_316
      v2 v6 v7
du_is'45'set'45'truncation'45'dependent'45'universal'45'property_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'truncation'45'dependent'45'universal'45'property_316 v0
                                                                     v1 v2
  = coe v1 v0 (\ v3 -> v2)
-- foundation.universal-property-set-truncation.is-set-truncation-is-set-quotient
d_is'45'set'45'truncation'45'is'45'set'45'quotient_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'truncation'45'is'45'set'45'quotient_342 v0 ~v1 v2
                                                       ~v3 ~v4 ~v5 v6 v7
  = du_is'45'set'45'truncation'45'is'45'set'45'quotient_342
      v0 v2 v6 v7
du_is'45'set'45'truncation'45'is'45'set'45'quotient_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'truncation'45'is'45'set'45'quotient_342 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp_332
      (coe v2 v1 v3)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_is'45'equiv'45'pr1'45'is'45'contr_72
         (coe
            (\ v4 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                 (coe
                    MAlonzo.Code.Qfoundation.QreflectingZ45ZmapsZ45ZequivalenceZ45Zrelations.du_is'45'prop'45'reflects'45'Eq'45'Rel_54
                    (coe v0) (coe v0) (coe v1) (coe v3) (coe v4))
                 erased)))
-- foundation.universal-property-set-truncation.is-set-quotient-is-set-truncation
d_is'45'set'45'quotient'45'is'45'set'45'truncation_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'quotient'45'is'45'set'45'truncation_370 v0 ~v1 v2
                                                       ~v3 ~v4 ~v5 v6 v7
  = du_is'45'set'45'quotient'45'is'45'set'45'truncation_370
      v0 v2 v6 v7
du_is'45'set'45'quotient'45'is'45'set'45'truncation_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'quotient'45'is'45'set'45'truncation_370 v0 v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'right'45'factor_458
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtypeZ45ZarithmeticZ45ZdependentZ45ZpairZ45Ztypes.du_is'45'equiv'45'pr1'45'is'45'contr_72
         (coe
            (\ v4 ->
               coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                 (coe
                    MAlonzo.Code.Qfoundation.QreflectingZ45ZmapsZ45ZequivalenceZ45Zrelations.du_is'45'prop'45'reflects'45'Eq'45'Rel_54
                    (coe v0) (coe v0) (coe v1) (coe v3) (coe v4))
                 erased)))
      (coe v2 v1 v3)
