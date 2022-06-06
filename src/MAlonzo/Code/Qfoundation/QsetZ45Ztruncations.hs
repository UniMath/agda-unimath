{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QsetZ45Ztruncations where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcartesianZ45ZproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZfunctionZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QmereZ45Zequality
import qualified MAlonzo.Code.Qfoundation.Qsets
import qualified MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Zquotients
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation

-- foundation.set-truncations.type-trunc-Set
d_type'45'trunc'45'Set_6
  = error
      "MAlonzo Runtime Error: postulate evaluated: foundation.set-truncations.type-trunc-Set"
-- foundation.set-truncations.is-set-type-trunc-Set
d_is'45'set'45'type'45'trunc'45'Set_12
  = error
      "MAlonzo Runtime Error: postulate evaluated: foundation.set-truncations.is-set-type-trunc-Set"
-- foundation.set-truncations.trunc-Set
d_trunc'45'Set_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_trunc'45'Set_16 v0 ~v1 = du_trunc'45'Set_16 v0
du_trunc'45'Set_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_trunc'45'Set_16 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'set'45'type'45'trunc'45'Set_12 v0 erased)
-- foundation.set-truncations.unit-trunc-Set
d_unit'45'trunc'45'Set_26
  = error
      "MAlonzo Runtime Error: postulate evaluated: foundation.set-truncations.unit-trunc-Set"
-- foundation.set-truncations.is-set-truncation-trunc-Set
d_is'45'set'45'truncation'45'trunc'45'Set_34
  = error
      "MAlonzo Runtime Error: postulate evaluated: foundation.set-truncations.is-set-truncation-trunc-Set"
-- foundation.set-truncations.equiv-universal-property-trunc-Set
d_equiv'45'universal'45'property'45'trunc'45'Set_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'universal'45'property'45'trunc'45'Set_44 v0 v1 ~v2 v3
  = du_equiv'45'universal'45'property'45'trunc'45'Set_44 v0 v1 v3
du_equiv'45'universal'45'property'45'trunc'45'Set_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'universal'45'property'45'trunc'45'Set_44 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.Qfoundation.Qsets.du_precomp'45'Set_254
         (coe d_unit'45'trunc'45'Set_26 v0 erased))
      (coe d_is'45'set'45'truncation'45'trunc'45'Set_34 v0 v1 erased v2)
-- foundation.set-truncations.universal-property-trunc-Set
d_universal'45'property'45'trunc'45'Set_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'trunc'45'Set_56 v0 v1 ~v2
  = du_universal'45'property'45'trunc'45'Set_56 v0 v1
du_universal'45'property'45'trunc'45'Set_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'trunc'45'Set_56 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_universal'45'property'45'is'45'set'45'truncation_144
      (coe v1) (coe v0) (coe d_unit'45'trunc'45'Set_26 v0 erased)
      (coe d_is'45'set'45'truncation'45'trunc'45'Set_34 v0 v1 erased)
-- foundation.set-truncations.map-universal-property-trunc-Set
d_map'45'universal'45'property'45'trunc'45'Set_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'45'universal'45'property'45'trunc'45'Set_68 v0 v1 ~v2 v3 v4
  = du_map'45'universal'45'property'45'trunc'45'Set_68 v0 v1 v3 v4
du_map'45'universal'45'property'45'trunc'45'Set_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'45'universal'45'property'45'trunc'45'Set_68 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_map'45'is'45'set'45'truncation_180
      (coe v0) (coe v1) (coe d_unit'45'trunc'45'Set_26 v0 erased)
      (coe
         (\ v4 ->
            coe d_is'45'set'45'truncation'45'trunc'45'Set_34 v0 v4 erased))
      (coe v2) (coe v3)
-- foundation.set-truncations.triangle-universal-property-trunc-Set
d_triangle'45'universal'45'property'45'trunc'45'Set_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'universal'45'property'45'trunc'45'Set_86 = erased
-- foundation.set-truncations.apply-universal-property-trunc-Set
d_apply'45'universal'45'property'45'trunc'45'Set_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny
d_apply'45'universal'45'property'45'trunc'45'Set_104 v0 v1 ~v2 v3
                                                     v4 v5
  = du_apply'45'universal'45'property'45'trunc'45'Set_104
      v0 v1 v3 v4 v5
du_apply'45'universal'45'property'45'trunc'45'Set_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny
du_apply'45'universal'45'property'45'trunc'45'Set_104 v0 v1 v2 v3
                                                      v4
  = coe
      du_map'45'universal'45'property'45'trunc'45'Set_68 v0 v1 v3 v4 v2
-- foundation.set-truncations.dependent-universal-property-trunc-Set
d_dependent'45'universal'45'property'45'trunc'45'Set_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'trunc'45'Set_118 v0 ~v1 ~v2
  = du_dependent'45'universal'45'property'45'trunc'45'Set_118 v0
du_dependent'45'universal'45'property'45'trunc'45'Set_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'trunc'45'Set_118 v0
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_dependent'45'universal'45'property'45'is'45'set'45'truncation_272
      (coe v0) (coe du_trunc'45'Set_16 (coe v0))
      (coe d_unit'45'trunc'45'Set_26 v0 erased)
      (coe
         (\ v1 ->
            coe d_is'45'set'45'truncation'45'trunc'45'Set_34 v0 v1 erased))
-- foundation.set-truncations.equiv-dependent-universal-property-trunc-Set
d_equiv'45'dependent'45'universal'45'property'45'trunc'45'Set_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'dependent'45'universal'45'property'45'trunc'45'Set_136 v0
                                                                  ~v1 ~v2 v3
  = du_equiv'45'dependent'45'universal'45'property'45'trunc'45'Set_136
      v0 v3
du_equiv'45'dependent'45'universal'45'property'45'trunc'45'Set_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'dependent'45'universal'45'property'45'trunc'45'Set_136 v0
                                                                   v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_precomp'45'Π'45'Set_70
         (coe d_unit'45'trunc'45'Set_26 v0 erased))
      (coe
         du_dependent'45'universal'45'property'45'trunc'45'Set_118 v0 v1)
-- foundation.set-truncations.apply-dependent-universal-property-trunc-Set
d_apply'45'dependent'45'universal'45'property'45'trunc'45'Set_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_apply'45'dependent'45'universal'45'property'45'trunc'45'Set_154 v0
                                                                  ~v1 ~v2 v3
  = du_apply'45'dependent'45'universal'45'property'45'trunc'45'Set_154
      v0 v3
du_apply'45'dependent'45'universal'45'property'45'trunc'45'Set_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_apply'45'dependent'45'universal'45'property'45'trunc'45'Set_154 v0
                                                                   v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'equiv_240
      (coe
         du_equiv'45'dependent'45'universal'45'property'45'trunc'45'Set_136
         (coe v0) (coe v1))
-- foundation.set-truncations.reflecting-map-mere-eq-unit-trunc-Set
d_reflecting'45'map'45'mere'45'eq'45'unit'45'trunc'45'Set_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_reflecting'45'map'45'mere'45'eq'45'unit'45'trunc'45'Set_162 v0
                                                              ~v1
  = du_reflecting'45'map'45'mere'45'eq'45'unit'45'trunc'45'Set_162 v0
du_reflecting'45'map'45'mere'45'eq'45'unit'45'trunc'45'Set_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_reflecting'45'map'45'mere'45'eq'45'unit'45'trunc'45'Set_162 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_unit'45'trunc'45'Set_26 v0 erased) erased
-- foundation.set-truncations.is-set-quotient-trunc-Set
d_is'45'set'45'quotient'45'trunc'45'Set_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'quotient'45'trunc'45'Set_172 v0 v1 ~v2
  = du_is'45'set'45'quotient'45'trunc'45'Set_172 v0 v1
du_is'45'set'45'quotient'45'trunc'45'Set_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'quotient'45'trunc'45'Set_172 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_is'45'set'45'quotient'45'is'45'set'45'truncation_370
      (coe v0) (coe v1)
      (coe
         (\ v2 ->
            coe d_is'45'set'45'truncation'45'trunc'45'Set_34 v0 v2 erased))
-- foundation.set-truncations.is-surjective-and-effective-unit-trunc-Set
d_is'45'surjective'45'and'45'effective'45'unit'45'trunc'45'Set_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'surjective'45'and'45'effective'45'unit'45'trunc'45'Set_182 v0
                                                                   ~v1
  = du_is'45'surjective'45'and'45'effective'45'unit'45'trunc'45'Set_182
      v0
du_is'45'surjective'45'and'45'effective'45'unit'45'trunc'45'Set_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'surjective'45'and'45'effective'45'unit'45'trunc'45'Set_182 v0
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Zquotients.du_is'45'surjective'45'and'45'effective'45'is'45'set'45'quotient_566
      (coe
         MAlonzo.Code.Qfoundation.QmereZ45Zequality.du_mere'45'eq'45'Eq'45'Rel_76
         (coe v0))
      (coe du_trunc'45'Set_16 (coe v0))
      (coe d_unit'45'trunc'45'Set_26 v0 erased)
      (coe
         (\ v1 ->
            coe
              du_is'45'set'45'quotient'45'trunc'45'Set_172 (coe v0) (coe v1)))
-- foundation.set-truncations.is-surjective-unit-trunc-Set
d_is'45'surjective'45'unit'45'trunc'45'Set_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> AgdaAny
d_is'45'surjective'45'unit'45'trunc'45'Set_192 v0 ~v1
  = du_is'45'surjective'45'unit'45'trunc'45'Set_192 v0
du_is'45'surjective'45'unit'45'trunc'45'Set_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny -> AgdaAny
du_is'45'surjective'45'unit'45'trunc'45'Set_192 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         du_is'45'surjective'45'and'45'effective'45'unit'45'trunc'45'Set_182
         (coe v0))
-- foundation.set-truncations.is-effective-unit-trunc-Set
d_is'45'effective'45'unit'45'trunc'45'Set_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'effective'45'unit'45'trunc'45'Set_200 v0 ~v1
  = du_is'45'effective'45'unit'45'trunc'45'Set_200 v0
du_is'45'effective'45'unit'45'trunc'45'Set_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'effective'45'unit'45'trunc'45'Set_200 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
      (coe
         du_is'45'surjective'45'and'45'effective'45'unit'45'trunc'45'Set_182
         (coe v0))
-- foundation.set-truncations.apply-effectiveness-unit-trunc-Set
d_apply'45'effectiveness'45'unit'45'trunc'45'Set_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_apply'45'effectiveness'45'unit'45'trunc'45'Set_212 v0 ~v1 v2 v3
  = du_apply'45'effectiveness'45'unit'45'trunc'45'Set_212 v0 v2 v3
du_apply'45'effectiveness'45'unit'45'trunc'45'Set_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
du_apply'45'effectiveness'45'unit'45'trunc'45'Set_212 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe du_is'45'effective'45'unit'45'trunc'45'Set_200 v0 v1 v2)
-- foundation.set-truncations.apply-effectiveness-unit-trunc-Set'
d_apply'45'effectiveness'45'unit'45'trunc'45'Set''_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_apply'45'effectiveness'45'unit'45'trunc'45'Set''_228 = erased
-- foundation.set-truncations.emb-trunc-Set
d_emb'45'trunc'45'Set_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_emb'45'trunc'45'Set_240 v0 ~v1 = du_emb'45'trunc'45'Set_240 v0
du_emb'45'trunc'45'Set_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_emb'45'trunc'45'Set_240 v0
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Zquotients.du_emb'45'is'45'surjective'45'and'45'effective_378
      (coe du_trunc'45'Set_16 (coe v0))
      (coe d_unit'45'trunc'45'Set_26 v0 erased)
      (coe
         du_is'45'surjective'45'and'45'effective'45'unit'45'trunc'45'Set_182
         (coe v0))
-- foundation.set-truncations.hom-slice-trunc-Set
d_hom'45'slice'45'trunc'45'Set_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_hom'45'slice'45'trunc'45'Set_248 v0 ~v1
  = du_hom'45'slice'45'trunc'45'Set_248 v0
du_hom'45'slice'45'trunc'45'Set_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_hom'45'slice'45'trunc'45'Set_248 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_unit'45'trunc'45'Set_26 v0 erased) erased
-- foundation.set-truncations.is-image-trunc-Set
d_is'45'image'45'trunc'45'Set_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'image'45'trunc'45'Set_258 v0 ~v1 ~v2
  = du_is'45'image'45'trunc'45'Set_258 v0
du_is'45'image'45'trunc'45'Set_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'image'45'trunc'45'Set_258 v0
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Zquotients.du_is'45'image'45'is'45'surjective'45'and'45'effective_418
      (coe v0) (coe v0)
      (coe
         MAlonzo.Code.Qfoundation.QmereZ45Zequality.du_mere'45'eq'45'Eq'45'Rel_76
         (coe v0))
      (coe du_trunc'45'Set_16 (coe v0))
      (coe d_unit'45'trunc'45'Set_26 v0 erased)
      (coe
         du_is'45'surjective'45'and'45'effective'45'unit'45'trunc'45'Set_182
         (coe v0))
-- foundation.set-truncations._.is-equiv-is-set-truncation'
d_is'45'equiv'45'is'45'set'45'truncation''_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'set'45'truncation''_282 v0 v1 ~v2 v3 v4 ~v5
                                               ~v6 ~v7
  = du_is'45'equiv'45'is'45'set'45'truncation''_282 v0 v1 v3 v4
du_is'45'equiv'45'is'45'set'45'truncation''_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'set'45'truncation''_282 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Ztruncations.du_is'45'equiv'45'is'45'set'45'truncation'45'is'45'set'45'truncation_32
      (coe v0) (coe v1) (coe v2) (coe v3)
      (coe d_unit'45'trunc'45'Set_26 v0 erased)
      (coe
         (\ v4 ->
            coe d_is'45'set'45'truncation'45'trunc'45'Set_34 v0 v4 erased))
-- foundation.set-truncations._.is-set-truncation-is-equiv'
d_is'45'set'45'truncation'45'is'45'equiv''_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'truncation'45'is'45'equiv''_290 v0 ~v1 ~v2 ~v3 ~v4
                                               v5 ~v6 v7 v8
  = du_is'45'set'45'truncation'45'is'45'equiv''_290 v0 v5 v7 v8
du_is'45'set'45'truncation'45'is'45'equiv''_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'truncation'45'is'45'equiv''_290 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Ztruncations.du_is'45'set'45'truncation'45'is'45'equiv'45'is'45'set'45'truncation_46
      (coe v0) (coe v1)
      (coe
         (\ v4 ->
            coe d_is'45'set'45'truncation'45'trunc'45'Set_34 v0 v4 erased))
      (coe v2) (coe v3)
-- foundation.set-truncations._.is-equiv-is-set-truncation
d_is'45'equiv'45'is'45'set'45'truncation_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'set'45'truncation_316 v0 ~v1 ~v2 ~v3 v4 ~v5
                                             ~v6 v7
  = du_is'45'equiv'45'is'45'set'45'truncation_316 v0 v4 v7
du_is'45'equiv'45'is'45'set'45'truncation_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'set'45'truncation_316 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Ztruncations.du_is'45'equiv'45'is'45'set'45'truncation'45'is'45'set'45'truncation_32
      (coe v0) (coe v0) (coe du_trunc'45'Set_16 (coe v0))
      (coe d_unit'45'trunc'45'Set_26 v0 erased) (coe v1) (coe v2)
-- foundation.set-truncations._.is-set-truncation-is-equiv
d_is'45'set'45'truncation'45'is'45'equiv_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'truncation'45'is'45'equiv_324 v0 ~v1 ~v2 ~v3 ~v4 v5
                                             ~v6 v7 v8
  = du_is'45'set'45'truncation'45'is'45'equiv_324 v0 v5 v7 v8
du_is'45'set'45'truncation'45'is'45'equiv_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'truncation'45'is'45'equiv_324 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Ztruncations.du_is'45'set'45'truncation'45'is'45'set'45'truncation'45'is'45'equiv_56
      (coe v0) (coe v1) (coe v2)
      (coe
         (\ v4 ->
            coe d_is'45'set'45'truncation'45'trunc'45'Set_34 v0 v4 erased))
      (coe v3)
-- foundation.set-truncations.is-equiv-unit-trunc-Set
d_is'45'equiv'45'unit'45'trunc'45'Set_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'unit'45'trunc'45'Set_334 v0 v1
  = coe
      du_is'45'equiv'45'is'45'set'45'truncation''_282 (coe v0) (coe v0)
      (coe v1) (coe (\ v2 -> v2))
-- foundation.set-truncations.equiv-unit-trunc-Set
d_equiv'45'unit'45'trunc'45'Set_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'unit'45'trunc'45'Set_342 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_unit'45'trunc'45'Set_26 v0 erased)
      (coe d_is'45'equiv'45'unit'45'trunc'45'Set_334 (coe v0) (coe v1))
-- foundation.set-truncations.equiv-unit-trunc-empty-Set
d_equiv'45'unit'45'trunc'45'empty'45'Set_346 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'unit'45'trunc'45'empty'45'Set_346
  = coe
      d_equiv'45'unit'45'trunc'45'Set_342 (coe ())
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.d_empty'45'Set_94)
-- foundation.set-truncations.is-empty-trunc-Set
d_is'45'empty'45'trunc'45'Set_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'trunc'45'Set_352 = erased
-- foundation.set-truncations.is-empty-is-empty-trunc-Set
d_is'45'empty'45'is'45'empty'45'trunc'45'Set_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'empty'45'is'45'empty'45'trunc'45'Set_362 = erased
-- foundation.set-truncations.equiv-unit-trunc-unit-Set
d_equiv'45'unit'45'trunc'45'unit'45'Set_366 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'unit'45'trunc'45'unit'45'Set_366
  = coe
      d_equiv'45'unit'45'trunc'45'Set_342 (coe ())
      (coe MAlonzo.Code.Qfoundation.QunitZ45Ztype.d_unit'45'Set_88)
-- foundation.set-truncations.is-contr-trunc-Set
d_is'45'contr'45'trunc'45'Set_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'trunc'45'Set_372 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_is'45'contr'45'equiv''_216
      (coe
         d_equiv'45'unit'45'trunc'45'Set_342 (coe v0)
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
            (coe v1)
            (coe
               MAlonzo.Code.Qfoundation.Qsets.du_is'45'set'45'is'45'contr_8 v0
               v2)))
      (coe v2)
-- foundation.set-truncations._.uniqueness-trunc-Set
d_uniqueness'45'trunc'45'Set_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_uniqueness'45'trunc'45'Set_400 v0 v1 ~v2 v3 v4 v5
  = du_uniqueness'45'trunc'45'Set_400 v0 v1 v3 v4 v5
du_uniqueness'45'trunc'45'Set_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_uniqueness'45'trunc'45'Set_400 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Ztruncations.du_uniqueness'45'set'45'truncation_92
      (coe v0) (coe v0) (coe v1) (coe du_trunc'45'Set_16 (coe v0))
      (coe d_unit'45'trunc'45'Set_26 v0 erased) (coe v2) (coe v3)
      (coe
         (\ v5 ->
            coe d_is'45'set'45'truncation'45'trunc'45'Set_34 v0 v5 erased))
      (coe v4)
-- foundation.set-truncations._.equiv-uniqueness-trunc-Set
d_equiv'45'uniqueness'45'trunc'45'Set_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'uniqueness'45'trunc'45'Set_404 v0 v1 ~v2 v3 v4 v5
  = du_equiv'45'uniqueness'45'trunc'45'Set_404 v0 v1 v3 v4 v5
du_equiv'45'uniqueness'45'trunc'45'Set_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'uniqueness'45'trunc'45'Set_404 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe
            du_uniqueness'45'trunc'45'Set_400 (coe v0) (coe v1) (coe v2)
            (coe v3) (coe v4)))
-- foundation.set-truncations._.map-equiv-uniqueness-trunc-Set
d_map'45'equiv'45'uniqueness'45'trunc'45'Set_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny
d_map'45'equiv'45'uniqueness'45'trunc'45'Set_406 v0 v1 ~v2 v3 v4 v5
  = du_map'45'equiv'45'uniqueness'45'trunc'45'Set_406 v0 v1 v3 v4 v5
du_map'45'equiv'45'uniqueness'45'trunc'45'Set_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny
du_map'45'equiv'45'uniqueness'45'trunc'45'Set_406 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe
         du_equiv'45'uniqueness'45'trunc'45'Set_404 (coe v0) (coe v1)
         (coe v2) (coe v3) (coe v4))
-- foundation.set-truncations._.triangle-uniqueness-trunc-Set
d_triangle'45'uniqueness'45'trunc'45'Set_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'uniqueness'45'trunc'45'Set_408 = erased
-- foundation.set-truncations._.uniqueness-trunc-Set'
d_uniqueness'45'trunc'45'Set''_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_uniqueness'45'trunc'45'Set''_430 v0 v1 ~v2 v3 v4 v5
  = du_uniqueness'45'trunc'45'Set''_430 v0 v1 v3 v4 v5
du_uniqueness'45'trunc'45'Set''_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_uniqueness'45'trunc'45'Set''_430 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Ztruncations.du_uniqueness'45'set'45'truncation_92
      (coe v0) (coe v1) (coe v0) (coe v2) (coe v3)
      (coe du_trunc'45'Set_16 (coe v0))
      (coe d_unit'45'trunc'45'Set_26 v0 erased) (coe v4)
      (coe
         (\ v5 ->
            coe d_is'45'set'45'truncation'45'trunc'45'Set_34 v0 v5 erased))
-- foundation.set-truncations._.equiv-uniqueness-trunc-Set'
d_equiv'45'uniqueness'45'trunc'45'Set''_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'uniqueness'45'trunc'45'Set''_434 v0 v1 ~v2 v3 v4 v5
  = du_equiv'45'uniqueness'45'trunc'45'Set''_434 v0 v1 v3 v4 v5
du_equiv'45'uniqueness'45'trunc'45'Set''_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'uniqueness'45'trunc'45'Set''_434 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe
            du_uniqueness'45'trunc'45'Set''_430 (coe v0) (coe v1) (coe v2)
            (coe v3) (coe v4)))
-- foundation.set-truncations._.map-equiv-uniqueness-trunc-Set'
d_map'45'equiv'45'uniqueness'45'trunc'45'Set''_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny
d_map'45'equiv'45'uniqueness'45'trunc'45'Set''_436 v0 v1 ~v2 v3 v4
                                                   v5
  = du_map'45'equiv'45'uniqueness'45'trunc'45'Set''_436
      v0 v1 v3 v4 v5
du_map'45'equiv'45'uniqueness'45'trunc'45'Set''_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny
du_map'45'equiv'45'uniqueness'45'trunc'45'Set''_436 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe
         du_equiv'45'uniqueness'45'trunc'45'Set''_434 (coe v0) (coe v1)
         (coe v2) (coe v3) (coe v4))
-- foundation.set-truncations._.triangle-uniqueness-trunc-Set'
d_triangle'45'uniqueness'45'trunc'45'Set''_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'uniqueness'45'trunc'45'Set''_438 = erased
-- foundation.set-truncations._.distributive-trunc-coprod-Set
d_distributive'45'trunc'45'coprod'45'Set_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_distributive'45'trunc'45'coprod'45'Set_454 v0 v1 ~v2 ~v3
  = du_distributive'45'trunc'45'coprod'45'Set_454 v0 v1
du_distributive'45'trunc'45'coprod'45'Set_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_distributive'45'trunc'45'coprod'45'Set_454 v0 v1
  = coe
      du_uniqueness'45'trunc'45'Set_400 (coe ()) (coe ())
      (coe
         MAlonzo.Code.Qfoundation.QequalityZ45ZcoproductZ45Ztypes.du_coprod'45'Set_388
         (coe du_trunc'45'Set_16 (coe v0))
         (coe du_trunc'45'Set_16 (coe v1)))
      (coe
         MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_map'45'coprod_24
         (coe d_unit'45'trunc'45'Set_26 v0 erased)
         (coe d_unit'45'trunc'45'Set_26 v1 erased))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'right'45'factor''_510
              (coe
                 MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZcoproductZ45Ztypes.du_ev'45'inl'45'inr_26)
              (coe
                 MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZcoproductZ45Ztypes.du_universal'45'property'45'coprod_78)
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp''_370
                 (coe
                    MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZcoproductZ45Ztypes.du_universal'45'property'45'coprod_78)
                 (coe
                    MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcartesianZ45ZproductZ45Ztypes.du_is'45'equiv'45'map'45'prod_204
                    (coe d_is'45'set'45'truncation'45'trunc'45'Set_34 v0 v2 erased v3)
                    (coe
                       d_is'45'set'45'truncation'45'trunc'45'Set_34 v1 v2 erased v3)))))
-- foundation.set-truncations._.equiv-distributive-trunc-coprod-Set
d_equiv'45'distributive'45'trunc'45'coprod'45'Set_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'distributive'45'trunc'45'coprod'45'Set_464 v0 v1 ~v2 ~v3
  = du_equiv'45'distributive'45'trunc'45'coprod'45'Set_464 v0 v1
du_equiv'45'distributive'45'trunc'45'coprod'45'Set_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'distributive'45'trunc'45'coprod'45'Set_464 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe
            du_distributive'45'trunc'45'coprod'45'Set_454 (coe v0) (coe v1)))
-- foundation.set-truncations._.map-equiv-distributive-trunc-coprod-Set
d_map'45'equiv'45'distributive'45'trunc'45'coprod'45'Set_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_map'45'equiv'45'distributive'45'trunc'45'coprod'45'Set_466 v0 v1
                                                             ~v2 ~v3
  = du_map'45'equiv'45'distributive'45'trunc'45'coprod'45'Set_466
      v0 v1
du_map'45'equiv'45'distributive'45'trunc'45'coprod'45'Set_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
du_map'45'equiv'45'distributive'45'trunc'45'coprod'45'Set_466 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe
         du_equiv'45'distributive'45'trunc'45'coprod'45'Set_464 (coe v0)
         (coe v1))
-- foundation.set-truncations._.triangle-distributive-trunc-coprod-Set
d_triangle'45'distributive'45'trunc'45'coprod'45'Set_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'distributive'45'trunc'45'coprod'45'Set_468 = erased
-- foundation.set-truncations._.trunc-Σ-Set
d_trunc'45'Σ'45'Set_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_trunc'45'Σ'45'Set_488 v0 v1 ~v2 ~v3
  = du_trunc'45'Σ'45'Set_488 v0 v1
du_trunc'45'Σ'45'Set_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_trunc'45'Σ'45'Set_488 v0 v1
  = coe
      du_uniqueness'45'trunc'45'Set_400 (coe ()) (coe ())
      (coe du_trunc'45'Set_16 (coe ()))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
         (coe (\ v2 -> coe d_unit'45'trunc'45'Set_26 () erased))
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QfunctorialityZ45ZdependentZ45ZpairZ45Ztypes.du_tot_24
            (coe (\ v2 -> coe d_unit'45'trunc'45'Set_26 v1 erased))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'right'45'factor''_510
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.du_ev'45'pair_76)
              (coe
                 MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZdependentZ45ZpairZ45Ztypes.du_is'45'equiv'45'ev'45'pair_16)
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'htpy'45'equiv_586
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                    (coe
                       MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes.du_equiv'45'map'45'Π_180
                       (coe v0)
                       (coe
                          (\ v4 ->
                             coe
                               du_equiv'45'universal'45'property'45'trunc'45'Set_44 (coe v1)
                               (coe v2) (coe v3))))
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                       (coe
                          MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'ev'45'pair_42)
                       (coe
                          du_equiv'45'universal'45'property'45'trunc'45'Set_44 (coe ())
                          (coe v2) (coe v3)))))))
-- foundation.set-truncations._.equiv-trunc-Σ-Set
d_equiv'45'trunc'45'Σ'45'Set_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'trunc'45'Σ'45'Set_504 v0 v1 ~v2 ~v3
  = du_equiv'45'trunc'45'Σ'45'Set_504 v0 v1
du_equiv'45'trunc'45'Σ'45'Set_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'trunc'45'Σ'45'Set_504 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe du_trunc'45'Σ'45'Set_488 (coe v0) (coe v1)))
-- foundation.set-truncations._.map-equiv-trunc-Σ-Set
d_map'45'equiv'45'trunc'45'Σ'45'Set_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> AgdaAny
d_map'45'equiv'45'trunc'45'Σ'45'Set_508 v0 v1 ~v2 ~v3
  = du_map'45'equiv'45'trunc'45'Σ'45'Set_508 v0 v1
du_map'45'equiv'45'trunc'45'Σ'45'Set_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny -> AgdaAny
du_map'45'equiv'45'trunc'45'Σ'45'Set_508 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe du_equiv'45'trunc'45'Σ'45'Set_504 (coe v0) (coe v1))
-- foundation.set-truncations._.distributive-trunc-prod-Set
d_distributive'45'trunc'45'prod'45'Set_524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_distributive'45'trunc'45'prod'45'Set_524 v0 v1 ~v2 ~v3
  = du_distributive'45'trunc'45'prod'45'Set_524 v0 v1
du_distributive'45'trunc'45'prod'45'Set_524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_distributive'45'trunc'45'prod'45'Set_524 v0 v1
  = coe
      du_uniqueness'45'trunc'45'Set_400 (coe ()) (coe ())
      (coe
         MAlonzo.Code.Qfoundation.Qsets.du_prod'45'Set_62
         (coe du_trunc'45'Set_16 (coe v0))
         (coe du_trunc'45'Set_16 (coe v1)))
      (coe
         MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcartesianZ45ZproductZ45Ztypes.du_map'45'prod_28
         (coe d_unit'45'trunc'45'Set_26 v0 erased)
         (coe d_unit'45'trunc'45'Set_26 v1 erased))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'right'45'factor''_510
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.du_ev'45'pair_76)
              (coe
                 MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZdependentZ45ZpairZ45Ztypes.du_is'45'equiv'45'ev'45'pair_16)
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'htpy'45'equiv_586
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                    (coe
                       du_equiv'45'universal'45'property'45'trunc'45'Set_44 (coe v0)
                       (coe ())
                       (coe
                          MAlonzo.Code.Qfoundation.Qsets.du_Π'45'Set''_138 (coe v1) (coe v2)
                          (coe (\ v4 -> v3))))
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
                       (coe
                          MAlonzo.Code.Qfoundation.QfunctorialityZ45ZfunctionZ45Ztypes.du_equiv'45'postcomp_164
                          (coe
                             du_equiv'45'universal'45'property'45'trunc'45'Set_44 (coe v1)
                             (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZdependentZ45ZpairZ45Ztypes.du_equiv'45'ev'45'pair_42))))))
-- foundation.set-truncations._.equiv-distributive-trunc-prod-Set
d_equiv'45'distributive'45'trunc'45'prod'45'Set_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'distributive'45'trunc'45'prod'45'Set_532 v0 v1 ~v2 ~v3
  = du_equiv'45'distributive'45'trunc'45'prod'45'Set_532 v0 v1
du_equiv'45'distributive'45'trunc'45'prod'45'Set_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'distributive'45'trunc'45'prod'45'Set_532 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe
            du_distributive'45'trunc'45'prod'45'Set_524 (coe v0) (coe v1)))
-- foundation.set-truncations._.map-equiv-distributive-trunc-prod-Set
d_map'45'equiv'45'distributive'45'trunc'45'prod'45'Set_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'equiv'45'distributive'45'trunc'45'prod'45'Set_534 v0 v1
                                                           ~v2 ~v3
  = du_map'45'equiv'45'distributive'45'trunc'45'prod'45'Set_534 v0 v1
du_map'45'equiv'45'distributive'45'trunc'45'prod'45'Set_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'equiv'45'distributive'45'trunc'45'prod'45'Set_534 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe
         du_equiv'45'distributive'45'trunc'45'prod'45'Set_532 (coe v0)
         (coe v1))
-- foundation.set-truncations._.triangle-distributive-trunc-prod-Set
d_triangle'45'distributive'45'trunc'45'prod'45'Set_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'distributive'45'trunc'45'prod'45'Set_536 = erased
