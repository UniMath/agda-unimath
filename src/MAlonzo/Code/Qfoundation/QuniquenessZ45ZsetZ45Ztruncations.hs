{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Ztruncations where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QmereZ45Zequality
import qualified MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Zquotients
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation

-- foundation.uniqueness-set-truncations._.is-equiv-is-set-truncation-is-set-truncation
d_is'45'equiv'45'is'45'set'45'truncation'45'is'45'set'45'truncation_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'set'45'truncation'45'is'45'set'45'truncation_32 v0
                                                                       v1 ~v2 ~v3 v4 v5 ~v6 v7 ~v8
                                                                       ~v9 ~v10 v11
  = du_is'45'equiv'45'is'45'set'45'truncation'45'is'45'set'45'truncation_32
      v0 v1 v4 v5 v7 v11
du_is'45'equiv'45'is'45'set'45'truncation'45'is'45'set'45'truncation_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'set'45'truncation'45'is'45'set'45'truncation_32 v0
                                                                        v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Zquotients.du_is'45'equiv'45'is'45'set'45'quotient'45'is'45'set'45'quotient_78
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Qfoundation.QmereZ45Zequality.du_reflecting'45'map'45'mere'45'eq_108
         (coe v3))
      (coe
         MAlonzo.Code.Qfoundation.QmereZ45Zequality.du_reflecting'45'map'45'mere'45'eq_108
         (coe v4))
      (coe
         (\ v6 ->
            coe
              MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_is'45'set'45'quotient'45'is'45'set'45'truncation_370
              (coe v0) (coe v6) (coe v5)))
-- foundation.uniqueness-set-truncations._.is-set-truncation-is-equiv-is-set-truncation
d_is'45'set'45'truncation'45'is'45'equiv'45'is'45'set'45'truncation_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'truncation'45'is'45'equiv'45'is'45'set'45'truncation_46 v0
                                                                       ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                                                       v8 ~v9 v10 v11 v12
  = du_is'45'set'45'truncation'45'is'45'equiv'45'is'45'set'45'truncation_46
      v0 v8 v10 v11 v12
du_is'45'set'45'truncation'45'is'45'equiv'45'is'45'set'45'truncation_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'truncation'45'is'45'equiv'45'is'45'set'45'truncation_46 v0
                                                                        v1 v2 v3 v4
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_is'45'set'45'truncation'45'is'45'set'45'quotient_342
      (coe v0) (coe v4)
      (coe
         MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Zquotients.du_is'45'set'45'quotient'45'is'45'equiv'45'is'45'set'45'quotient_120
         (coe v1)
         (coe
            (\ v5 ->
               coe
                 MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_is'45'set'45'quotient'45'is'45'set'45'truncation_370
                 (coe v0) (coe v5) (coe v2)))
         (coe v3))
-- foundation.uniqueness-set-truncations._.is-set-truncation-is-set-truncation-is-equiv
d_is'45'set'45'truncation'45'is'45'set'45'truncation'45'is'45'equiv_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'truncation'45'is'45'set'45'truncation'45'is'45'equiv_56 v0
                                                                       ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                                                       v8 ~v9 v10 v11 v12
  = du_is'45'set'45'truncation'45'is'45'set'45'truncation'45'is'45'equiv_56
      v0 v8 v10 v11 v12
du_is'45'set'45'truncation'45'is'45'set'45'truncation'45'is'45'equiv_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'truncation'45'is'45'set'45'truncation'45'is'45'equiv_56 v0
                                                                        v1 v2 v3 v4
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_is'45'set'45'truncation'45'is'45'set'45'quotient_342
      (coe v0) (coe v4)
      (coe
         MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Zquotients.du_is'45'set'45'quotient'45'is'45'set'45'quotient'45'is'45'equiv_104
         (coe v1) (coe v2)
         (coe
            (\ v5 ->
               coe
                 MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_is'45'set'45'quotient'45'is'45'set'45'truncation_370
                 (coe v0) (coe v5) (coe v3))))
-- foundation.uniqueness-set-truncations._.uniqueness-set-truncation
d_uniqueness'45'set'45'truncation_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_uniqueness'45'set'45'truncation_92 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_uniqueness'45'set'45'truncation_92 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_uniqueness'45'set'45'truncation_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_uniqueness'45'set'45'truncation_92 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Qfoundation.QuniquenessZ45ZsetZ45Zquotients.du_uniqueness'45'set'45'quotient_166
      (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Qfoundation.QmereZ45Zequality.du_reflecting'45'map'45'mere'45'eq_108
         (coe v4))
      (coe
         (\ v9 ->
            coe
              MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_is'45'set'45'quotient'45'is'45'set'45'truncation_370
              (coe v0) (coe v9) (coe v7)))
      (coe v5)
      (coe
         MAlonzo.Code.Qfoundation.QmereZ45Zequality.du_reflecting'45'map'45'mere'45'eq_108
         (coe v6))
      (coe
         (\ v9 ->
            coe
              MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZsetZ45Ztruncation.du_is'45'set'45'quotient'45'is'45'set'45'truncation_370
              (coe v0) (coe v9) (coe v8)))
-- foundation.uniqueness-set-truncations._.equiv-uniqueness-set-truncation
d_equiv'45'uniqueness'45'set'45'truncation_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'uniqueness'45'set'45'truncation_94 v0 v1 v2 ~v3 v4 v5 v6
                                              v7 v8 v9
  = du_equiv'45'uniqueness'45'set'45'truncation_94
      v0 v1 v2 v4 v5 v6 v7 v8 v9
du_equiv'45'uniqueness'45'set'45'truncation_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'uniqueness'45'set'45'truncation_94 v0 v1 v2 v3 v4 v5 v6
                                               v7 v8
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe
            du_uniqueness'45'set'45'truncation_92 (coe v0) (coe v1) (coe v2)
            (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)))
-- foundation.uniqueness-set-truncations._.map-equiv-uniqueness-set-truncation
d_map'45'equiv'45'uniqueness'45'set'45'truncation_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny
d_map'45'equiv'45'uniqueness'45'set'45'truncation_96 v0 v1 v2 ~v3
                                                     v4 v5 v6 v7 v8 v9
  = du_map'45'equiv'45'uniqueness'45'set'45'truncation_96
      v0 v1 v2 v4 v5 v6 v7 v8 v9
du_map'45'equiv'45'uniqueness'45'set'45'truncation_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny
du_map'45'equiv'45'uniqueness'45'set'45'truncation_96 v0 v1 v2 v3
                                                      v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe
         du_equiv'45'uniqueness'45'set'45'truncation_94 (coe v0) (coe v1)
         (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8))
-- foundation.uniqueness-set-truncations._.triangle-uniqueness-set-truncation
d_triangle'45'uniqueness'45'set'45'truncation_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_triangle'45'uniqueness'45'set'45'truncation_98 = erased
