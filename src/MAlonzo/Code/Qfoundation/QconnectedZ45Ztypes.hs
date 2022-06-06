{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QconnectedZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qsets
import qualified MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QmereZ45Zequality
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QsetZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QsurjectiveZ45Zmaps
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZunitZ45Ztype

-- foundation.connected-types.is-path-connected-Prop
d_is'45'path'45'connected'45'Prop_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'path'45'connected'45'Prop_6 ~v0 ~v1
  = du_is'45'path'45'connected'45'Prop_6
du_is'45'path'45'connected'45'Prop_6 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'path'45'connected'45'Prop_6
  = coe
      MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes.du_is'45'contr'45'Prop_108
-- foundation.connected-types.is-path-connected
d_is'45'path'45'connected_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_is'45'path'45'connected_12 = erased
-- foundation.connected-types.is-inhabited-is-path-connected
d_is'45'inhabited'45'is'45'path'45'connected_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'inhabited'45'is'45'path'45'connected_20 v0 ~v1 v2
  = du_is'45'inhabited'45'is'45'path'45'connected_20 v0 v2
du_is'45'inhabited'45'is'45'path'45'connected_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_is'45'inhabited'45'is'45'path'45'connected_20 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QsetZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Set_104
      (coe v0) (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe v1))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qsets.d_set'45'Prop_160 (coe v0)
         (coe
            MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
            v0 erased))
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
         (coe v0))
-- foundation.connected-types.mere-eq-is-path-connected
d_mere'45'eq'45'is'45'path'45'connected_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_mere'45'eq'45'is'45'path'45'connected_36 v0 ~v1 ~v2 v3 v4
  = du_mere'45'eq'45'is'45'path'45'connected_36 v0 v3 v4
du_mere'45'eq'45'is'45'path'45'connected_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_mere'45'eq'45'is'45'path'45'connected_36 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QsetZ45Ztruncations.du_apply'45'effectiveness'45'unit'45'trunc'45'Set_212
      v0 v1 v2 erased
-- foundation.connected-types.is-path-connected-mere-eq
d_is'45'path'45'connected'45'mere'45'eq_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'path'45'connected'45'mere'45'eq_54 v0 ~v1 v2 ~v3
  = du_is'45'path'45'connected'45'mere'45'eq_54 v0 v2
du_is'45'path'45'connected'45'mere'45'eq_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'path'45'connected'45'mere'45'eq_54 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.Qfoundation.QsetZ45Ztruncations.d_unit'45'trunc'45'Set_26
         v0 erased v1)
      (coe
         MAlonzo.Code.Qfoundation.QsetZ45Ztruncations.du_apply'45'dependent'45'universal'45'property'45'trunc'45'Set_154
         v0
         (\ v2 ->
            MAlonzo.Code.QfoundationZ45Zcore.Qsets.d_set'45'Prop_160
              (coe v0)
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qsets.du_Id'45'Prop_36
                 (coe
                    MAlonzo.Code.Qfoundation.QsetZ45Ztruncations.du_trunc'45'Set_16
                    (coe v0))
                 (coe
                    MAlonzo.Code.Qfoundation.QsetZ45Ztruncations.d_unit'45'trunc'45'Set_26
                    v0 erased v1)
                 (coe v2)))
         erased)
-- foundation.connected-types.is-path-connected-is-surjective-pt
d_is'45'path'45'connected'45'is'45'surjective'45'pt_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'path'45'connected'45'is'45'surjective'45'pt_74 v0 ~v1 v2
                                                       ~v3
  = du_is'45'path'45'connected'45'is'45'surjective'45'pt_74 v0 v2
du_is'45'path'45'connected'45'is'45'surjective'45'pt_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'path'45'connected'45'is'45'surjective'45'pt_74 v0 v1
  = coe du_is'45'path'45'connected'45'mere'45'eq_54 (coe v0) (coe v1)
-- foundation.connected-types.is-surjective-pt-is-path-connected
d_is'45'surjective'45'pt'45'is'45'path'45'connected_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_is'45'surjective'45'pt'45'is'45'path'45'connected_90 v0 ~v1 v2
                                                       ~v3 v4
  = du_is'45'surjective'45'pt'45'is'45'path'45'connected_90 v0 v2 v4
du_is'45'surjective'45'pt'45'is'45'path'45'connected_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_is'45'surjective'45'pt'45'is'45'path'45'connected_90 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe v0) (coe v0)
      (coe
         du_mere'45'eq'45'is'45'path'45'connected_36 (coe v0) (coe v1)
         (coe v2))
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
         v0 erased)
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
              v0
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                 erased erased)))
-- foundation.connected-types.equiv-dependent-universal-property-is-path-connected
d_equiv'45'dependent'45'universal'45'property'45'is'45'path'45'connected_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'dependent'45'universal'45'property'45'is'45'path'45'connected_112 v0
                                                                             ~v1 v2 ~v3 v4 v5
  = du_equiv'45'dependent'45'universal'45'property'45'is'45'path'45'connected_112
      v0 v2 v4 v5
du_equiv'45'dependent'45'universal'45'property'45'is'45'path'45'connected_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'dependent'45'universal'45'property'45'is'45'path'45'connected_112 v0
                                                                              v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZunitZ45Ztype.du_equiv'45'universal'45'property'45'unit_70)
      (coe
         MAlonzo.Code.Qfoundation.QsurjectiveZ45Zmaps.du_equiv'45'dependent'45'universal'45'property'45'surj'45'is'45'surjective_216
         (coe v2) (coe v0) (coe (\ v4 -> v1))
         (coe
            du_is'45'surjective'45'pt'45'is'45'path'45'connected_90 (coe v0)
            (coe v1))
         (coe v3))
-- foundation.connected-types.apply-dependent-universal-property-is-path-connected
d_apply'45'dependent'45'universal'45'property'45'is'45'path'45'connected_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_apply'45'dependent'45'universal'45'property'45'is'45'path'45'connected_132 v0
                                                                             ~v1 v2 ~v3 v4 v5
  = du_apply'45'dependent'45'universal'45'property'45'is'45'path'45'connected_132
      v0 v2 v4 v5
du_apply'45'dependent'45'universal'45'property'45'is'45'path'45'connected_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_apply'45'dependent'45'universal'45'property'45'is'45'path'45'connected_132 v0
                                                                              v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'equiv_240
      (coe
         du_equiv'45'dependent'45'universal'45'property'45'is'45'path'45'connected_112
         (coe v0) (coe v1) (coe v2) (coe v3))
-- foundation.connected-types.is-surjective-fiber-inclusion
d_is'45'surjective'45'fiber'45'inclusion_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'surjective'45'fiber'45'inclusion_150 v0 ~v1 ~v2 ~v3 ~v4 v5
                                             v6
  = du_is'45'surjective'45'fiber'45'inclusion_150 v0 v5 v6
du_is'45'surjective'45'fiber'45'inclusion_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_is'45'surjective'45'fiber'45'inclusion_150 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v3 v4
        -> coe
             MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
             (coe v0) (coe ())
             (coe
                du_mere'45'eq'45'is'45'path'45'connected_36 (coe v0) (coe v1)
                (coe v3))
             (coe
                MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
                () erased)
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
                     ()
                     (coe
                        MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                        (coe v4) erased)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.connected-types.mere-eq-is-surjective-fiber-inclusion
d_mere'45'eq'45'is'45'surjective'45'fiber'45'inclusion_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   AgdaAny) ->
  AgdaAny -> AgdaAny
d_mere'45'eq'45'is'45'surjective'45'fiber'45'inclusion_176 v0 ~v1
                                                           ~v2 v3 v4
  = du_mere'45'eq'45'is'45'surjective'45'fiber'45'inclusion_176
      v0 v3 v4
du_mere'45'eq'45'is'45'surjective'45'fiber'45'inclusion_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   AgdaAny) ->
  AgdaAny -> AgdaAny
du_mere'45'eq'45'is'45'surjective'45'fiber'45'inclusion_176 v0 v1
                                                            v2
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe v0) (coe v0)
      (coe
         v1 () erased
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
            (coe v2) erased))
      (coe
         MAlonzo.Code.Qfoundation.QmereZ45Zequality.du_mere'45'eq'45'Prop_8
         (coe v0))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
              v0 erased))
-- foundation.connected-types.is-path-connected-is-surjective-fiber-inclusion
d_is'45'path'45'connected'45'is'45'surjective'45'fiber'45'inclusion_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny -> ()) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'path'45'connected'45'is'45'surjective'45'fiber'45'inclusion_198 v0
                                                                        ~v1 v2 ~v3
  = du_is'45'path'45'connected'45'is'45'surjective'45'fiber'45'inclusion_198
      v0 v2
du_is'45'path'45'connected'45'is'45'surjective'45'fiber'45'inclusion_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'path'45'connected'45'is'45'surjective'45'fiber'45'inclusion_198 v0
                                                                         v1
  = coe du_is'45'path'45'connected'45'mere'45'eq_54 (coe v0) (coe v1)
