{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QequivalencesZ45Zmaybe where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qmaybe
import qualified MAlonzo.Code.Qfoundation.QunitZ45Ztype
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Zmaybe

-- foundation.equivalences-maybe.equiv-Maybe
d_equiv'45'Maybe_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'Maybe_14 ~v0 ~v1 ~v2 ~v3 v4 = du_equiv'45'Maybe_14 v4
du_equiv'45'Maybe_14 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'Maybe_14 v0
  = coe
      MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_equiv'45'coprod_242
      (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)
-- foundation.equivalences-maybe.equiv-maybe-structure
d_equiv'45'maybe'45'structure_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_equiv'45'maybe'45'structure_26 = erased
-- foundation.equivalences-maybe.id-equiv-maybe-structure
d_id'45'equiv'45'maybe'45'structure_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_id'45'equiv'45'maybe'45'structure_40 ~v0 ~v1 ~v2
  = du_id'45'equiv'45'maybe'45'structure_40
du_id'45'equiv'45'maybe'45'structure_40 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_id'45'equiv'45'maybe'45'structure_40
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92)
      (coe
         MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Zmaybe.du_ind'45'Maybe_32
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
            erased erased))
-- foundation.equivalences-maybe.equiv-eq-maybe-structure
d_equiv'45'eq'45'maybe'45'structure_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'eq'45'maybe'45'structure_52 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_equiv'45'eq'45'maybe'45'structure_52
du_equiv'45'eq'45'maybe'45'structure_52 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'eq'45'maybe'45'structure_52
  = coe du_id'45'equiv'45'maybe'45'structure_40
-- foundation.equivalences-maybe.is-not-exception-injective-map-exception-Maybe
d_is'45'not'45'exception'45'injective'45'map'45'exception'45'Maybe_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'not'45'exception'45'injective'45'map'45'exception'45'Maybe_68
  = erased
-- foundation.equivalences-maybe.is-not-exception-map-equiv-exception-Maybe
d_is'45'not'45'exception'45'map'45'equiv'45'exception'45'Maybe_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'not'45'exception'45'map'45'equiv'45'exception'45'Maybe_90
  = erased
-- foundation.equivalences-maybe.is-not-exception-emb-exception-Maybe
d_is'45'not'45'exception'45'emb'45'exception'45'Maybe_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'not'45'exception'45'emb'45'exception'45'Maybe_106 = erased
-- foundation.equivalences-maybe.is-value-injective-map-exception-Maybe
d_is'45'value'45'injective'45'map'45'exception'45'Maybe_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'value'45'injective'45'map'45'exception'45'Maybe_122 ~v0 ~v1
                                                            ~v2 ~v3 v4 ~v5 ~v6 ~v7
  = du_is'45'value'45'injective'45'map'45'exception'45'Maybe_122 v4
du_is'45'value'45'injective'45'map'45'exception'45'Maybe_122 ::
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'value'45'injective'45'map'45'exception'45'Maybe_122 v0
  = coe
      MAlonzo.Code.Qfoundation.Qmaybe.du_is'45'value'45'is'45'not'45'exception'45'Maybe_192
      (coe
         v0 (coe MAlonzo.Code.Qfoundation.Qmaybe.du_exception'45'Maybe_20))
-- foundation.equivalences-maybe.value-injective-map-exception-Maybe
d_value'45'injective'45'map'45'exception'45'Maybe_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_value'45'injective'45'map'45'exception'45'Maybe_144 ~v0 ~v1 ~v2
                                                      ~v3 v4 ~v5 ~v6 ~v7
  = du_value'45'injective'45'map'45'exception'45'Maybe_144 v4
du_value'45'injective'45'map'45'exception'45'Maybe_144 ::
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny
du_value'45'injective'45'map'45'exception'45'Maybe_144 v0
  = coe
      MAlonzo.Code.Qfoundation.Qmaybe.du_value'45'is'45'value'45'Maybe_66
      (coe
         du_is'45'value'45'injective'45'map'45'exception'45'Maybe_122
         (coe v0))
-- foundation.equivalences-maybe.comp-injective-map-exception-Maybe
d_comp'45'injective'45'map'45'exception'45'Maybe_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'injective'45'map'45'exception'45'Maybe_170 = erased
-- foundation.equivalences-maybe.is-value-map-equiv-exception-Maybe
d_is'45'value'45'map'45'equiv'45'exception'45'Maybe_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'value'45'map'45'equiv'45'exception'45'Maybe_192 ~v0 ~v1 ~v2
                                                        ~v3 v4 ~v5 ~v6
  = du_is'45'value'45'map'45'equiv'45'exception'45'Maybe_192 v4
du_is'45'value'45'map'45'equiv'45'exception'45'Maybe_192 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'value'45'map'45'equiv'45'exception'45'Maybe_192 v0
  = coe
      MAlonzo.Code.Qfoundation.Qmaybe.du_is'45'value'45'is'45'not'45'exception'45'Maybe_192
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
         v0 (coe MAlonzo.Code.Qfoundation.Qmaybe.du_exception'45'Maybe_20))
-- foundation.equivalences-maybe.value-map-equiv-exception-Maybe
d_value'45'map'45'equiv'45'exception'45'Maybe_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_value'45'map'45'equiv'45'exception'45'Maybe_212 ~v0 ~v1 ~v2 ~v3
                                                  v4 ~v5 ~v6
  = du_value'45'map'45'equiv'45'exception'45'Maybe_212 v4
du_value'45'map'45'equiv'45'exception'45'Maybe_212 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_value'45'map'45'equiv'45'exception'45'Maybe_212 v0
  = coe
      MAlonzo.Code.Qfoundation.Qmaybe.du_value'45'is'45'value'45'Maybe_66
      (coe
         du_is'45'value'45'map'45'equiv'45'exception'45'Maybe_192 (coe v0))
-- foundation.equivalences-maybe.comp-map-equiv-exception-Maybe
d_comp'45'map'45'equiv'45'exception'45'Maybe_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'map'45'equiv'45'exception'45'Maybe_234 = erased
-- foundation.equivalences-maybe.restrict-injective-map-Maybe'
d_restrict'45'injective'45'map'45'Maybe''_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_restrict'45'injective'45'map'45'Maybe''_258 ~v0 ~v1 ~v2 ~v3 v4
                                              ~v5 ~v6 v7 ~v8
  = du_restrict'45'injective'45'map'45'Maybe''_258 v4 v7
du_restrict'45'injective'45'map'45'Maybe''_258 ::
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
du_restrict'45'injective'45'map'45'Maybe''_258 v0 v1
  = case coe v1 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2 -> coe v2
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> coe
             du_value'45'injective'45'map'45'exception'45'Maybe_144 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.equivalences-maybe.restrict-injective-map-Maybe
d_restrict'45'injective'45'map'45'Maybe_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny -> AgdaAny
d_restrict'45'injective'45'map'45'Maybe_288 ~v0 ~v1 ~v2 ~v3 v4 ~v5
                                            v6
  = du_restrict'45'injective'45'map'45'Maybe_288 v4 v6
du_restrict'45'injective'45'map'45'Maybe_288 ::
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  AgdaAny -> AgdaAny
du_restrict'45'injective'45'map'45'Maybe_288 v0 v1
  = coe
      du_restrict'45'injective'45'map'45'Maybe''_258 (coe v0)
      (coe
         v0
         (coe
            MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v1)))
-- foundation.equivalences-maybe.comp-restrict-injective-map-is-exception-Maybe'
d_comp'45'restrict'45'injective'45'map'45'is'45'exception'45'Maybe''_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'restrict'45'injective'45'map'45'is'45'exception'45'Maybe''_314
  = erased
-- foundation.equivalences-maybe.comp-restrict-injective-map-is-exception-Maybe
d_comp'45'restrict'45'injective'45'map'45'is'45'exception'45'Maybe_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'restrict'45'injective'45'map'45'is'45'exception'45'Maybe_352
  = erased
-- foundation.equivalences-maybe.comp-restrict-injective-map-is-not-exception-Maybe'
d_comp'45'restrict'45'injective'45'map'45'is'45'not'45'exception'45'Maybe''_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'restrict'45'injective'45'map'45'is'45'not'45'exception'45'Maybe''_378
  = erased
-- foundation.equivalences-maybe.comp-restrict-injective-map-is-not-exception-Maybe
d_comp'45'restrict'45'injective'45'map'45'is'45'not'45'exception'45'Maybe_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12) ->
  (MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'restrict'45'injective'45'map'45'is'45'not'45'exception'45'Maybe_412
  = erased
-- foundation.equivalences-maybe.map-equiv-equiv-Maybe'
d_map'45'equiv'45'equiv'45'Maybe''_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_map'45'equiv'45'equiv'45'Maybe''_436 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'equiv'45'equiv'45'Maybe''_436 v4
du_map'45'equiv'45'equiv'45'Maybe''_436 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
du_map'45'equiv'45'equiv'45'Maybe''_436 v0 v1 v2 v3
  = coe
      du_restrict'45'injective'45'map'45'Maybe''_258
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe v0))
      v2
-- foundation.equivalences-maybe.map-equiv-equiv-Maybe
d_map'45'equiv'45'equiv'45'Maybe_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'equiv'45'equiv'45'Maybe_450 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'equiv'45'equiv'45'Maybe_450 v4
du_map'45'equiv'45'equiv'45'Maybe_450 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'equiv'45'equiv'45'Maybe_450 v0
  = coe
      du_restrict'45'injective'45'map'45'Maybe_288
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe v0))
-- foundation.equivalences-maybe.comp-map-equiv-equiv-is-exception-Maybe'
d_comp'45'map'45'equiv'45'equiv'45'is'45'exception'45'Maybe''_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'map'45'equiv'45'equiv'45'is'45'exception'45'Maybe''_470
  = erased
-- foundation.equivalences-maybe.comp-map-equiv-equiv-is-exception-Maybe
d_comp'45'map'45'equiv'45'equiv'45'is'45'exception'45'Maybe_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'map'45'equiv'45'equiv'45'is'45'exception'45'Maybe_486
  = erased
-- foundation.equivalences-maybe.comp-map-equiv-equiv-is-not-exception-Maybe'
d_comp'45'map'45'equiv'45'equiv'45'is'45'not'45'exception'45'Maybe''_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'map'45'equiv'45'equiv'45'is'45'not'45'exception'45'Maybe''_508
  = erased
-- foundation.equivalences-maybe.comp-map-equiv-equiv-is-not-exception-Maybe
d_comp'45'map'45'equiv'45'equiv'45'is'45'not'45'exception'45'Maybe_540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'map'45'equiv'45'equiv'45'is'45'not'45'exception'45'Maybe_540
  = erased
-- foundation.equivalences-maybe.map-inv-equiv-equiv-Maybe
d_map'45'inv'45'equiv'45'equiv'45'Maybe_556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_map'45'inv'45'equiv'45'equiv'45'Maybe_556 ~v0 ~v1 ~v2 ~v3 v4
  = du_map'45'inv'45'equiv'45'equiv'45'Maybe_556 v4
du_map'45'inv'45'equiv'45'equiv'45'Maybe_556 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_map'45'inv'45'equiv'45'equiv'45'Maybe_556 v0
  = coe
      du_map'45'equiv'45'equiv'45'Maybe_450
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_inv'45'equiv_250
         (coe v0))
-- foundation.equivalences-maybe.comp-map-inv-equiv-equiv-is-exception-Maybe
d_comp'45'map'45'inv'45'equiv'45'equiv'45'is'45'exception'45'Maybe_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'map'45'inv'45'equiv'45'equiv'45'is'45'exception'45'Maybe_572
  = erased
-- foundation.equivalences-maybe.comp-map-inv-equiv-equiv-is-not-exception-Maybe
d_comp'45'map'45'inv'45'equiv'45'equiv'45'is'45'not'45'exception'45'Maybe_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'map'45'inv'45'equiv'45'equiv'45'is'45'not'45'exception'45'Maybe_590
  = erased
-- foundation.equivalences-maybe.issec-map-inv-equiv-equiv-Maybe
d_issec'45'map'45'inv'45'equiv'45'equiv'45'Maybe_604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'map'45'inv'45'equiv'45'equiv'45'Maybe_604 = erased
-- foundation.equivalences-maybe.isretr-map-inv-equiv-equiv-Maybe
d_isretr'45'map'45'inv'45'equiv'45'equiv'45'Maybe_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'map'45'inv'45'equiv'45'equiv'45'Maybe_636 = erased
-- foundation.equivalences-maybe.is-equiv-map-equiv-equiv-Maybe
d_is'45'equiv'45'map'45'equiv'45'equiv'45'Maybe_668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'equiv'45'equiv'45'Maybe_668 ~v0 ~v1 ~v2 ~v3
                                                    v4
  = du_is'45'equiv'45'map'45'equiv'45'equiv'45'Maybe_668 v4
du_is'45'equiv'45'map'45'equiv'45'equiv'45'Maybe_668 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'equiv'45'equiv'45'Maybe_668 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
      (coe du_map'45'inv'45'equiv'45'equiv'45'Maybe_556 (coe v0)) erased
      erased
-- foundation.equivalences-maybe.equiv-equiv-Maybe
d_equiv'45'equiv'45'Maybe_680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'equiv'45'Maybe_680 ~v0 ~v1 ~v2 ~v3 v4
  = du_equiv'45'equiv'45'Maybe_680 v4
du_equiv'45'equiv'45'Maybe_680 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'equiv'45'Maybe_680 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'equiv'45'equiv'45'Maybe_450 (coe v0))
      (coe du_is'45'equiv'45'map'45'equiv'45'equiv'45'Maybe_668 (coe v0))
-- foundation.equivalences-maybe._.extend-equiv-Maybe
d_extend'45'equiv'45'Maybe_696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_extend'45'equiv'45'Maybe_696 ~v0 ~v1
  = du_extend'45'equiv'45'Maybe_696
du_extend'45'equiv'45'Maybe_696 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_extend'45'equiv'45'Maybe_696
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
              (coe
                 MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_equiv'45'coprod_242
                 (coe v0)
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_id'45'equiv_92))
              erased))
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'has'45'inverse_140
         (coe
            (\ v0 ->
               MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                 (coe
                    MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcoproductZ45Ztypes.du_retr'45'equiv'45'coprod_590
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                       (coe v0))
                    erased)))
         erased erased)
-- foundation.equivalences-maybe._._.p
d_p_712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QunitZ45Ztype.T_unit_4 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_p_712 = erased
-- foundation.equivalences-maybe._.computation-extend-equiv-Maybe
d_computation'45'extend'45'equiv'45'Maybe_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_computation'45'extend'45'equiv'45'Maybe_728 = erased
-- foundation.equivalences-maybe._.computation-inv-extend-equiv-Maybe
d_computation'45'inv'45'extend'45'equiv'45'Maybe_744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_computation'45'inv'45'extend'45'equiv'45'Maybe_744 = erased
-- foundation.equivalences-maybe._.comp-extend-equiv-Maybe
d_comp'45'extend'45'equiv'45'Maybe_756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'extend'45'equiv'45'Maybe_756 = erased
