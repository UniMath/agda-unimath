{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45Zarithmetic where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45Zintegers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes

-- elementary-number-theory.modular-arithmetic.ℤ-Mod
d_ℤ'45'Mod_4 :: Integer -> ()
d_ℤ'45'Mod_4 = erased
-- elementary-number-theory.modular-arithmetic.zero-ℤ-Mod
d_zero'45'ℤ'45'Mod_10 :: Integer -> AgdaAny
d_zero'45'ℤ'45'Mod_10 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_zero'45'ℤ_16
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_zero'45'Fin_230
             (coe v1)
-- elementary-number-theory.modular-arithmetic.is-zero-ℤ-Mod
d_is'45'zero'45'ℤ'45'Mod_16 :: Integer -> AgdaAny -> ()
d_is'45'zero'45'ℤ'45'Mod_16 = erased
-- elementary-number-theory.modular-arithmetic.is-nonzero-ℤ-Mod
d_is'45'nonzero'45'ℤ'45'Mod_24 :: Integer -> AgdaAny -> ()
d_is'45'nonzero'45'ℤ'45'Mod_24 = erased
-- elementary-number-theory.modular-arithmetic.neg-one-ℤ-Mod
d_neg'45'one'45'ℤ'45'Mod_32 :: Integer -> AgdaAny
d_neg'45'one'45'ℤ'45'Mod_32 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'one'45'ℤ_10
      _ -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.du_neg'45'one'45'Fin_24
-- elementary-number-theory.modular-arithmetic.one-ℤ-Mod
d_one'45'ℤ'45'Mod_38 :: Integer -> AgdaAny
d_one'45'ℤ'45'Mod_38 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_one'45'ℤ_30
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_one'45'Fin_308
             (coe v1)
-- elementary-number-theory.modular-arithmetic.has-decidable-equality-ℤ-Mod
d_has'45'decidable'45'equality'45'ℤ'45'Mod_44 ::
  Integer ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_has'45'decidable'45'equality'45'ℤ'45'Mod_44 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45Zintegers.d_has'45'decidable'45'equality'45'ℤ_72
      _ -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes.du_has'45'decidable'45'equality'45'Fin_112
-- elementary-number-theory.modular-arithmetic.is-set-ℤ-Mod
d_is'45'set'45'ℤ'45'Mod_50 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'ℤ'45'Mod_50 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45Zintegers.d_is'45'set'45'ℤ_92
      _ -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes.d_is'45'set'45'Fin_152
             (coe v0)
-- elementary-number-theory.modular-arithmetic.ℤ-Mod-Set
d_ℤ'45'Mod'45'Set_56 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_ℤ'45'Mod'45'Set_56 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased (coe d_is'45'set'45'ℤ'45'Mod_50 (coe v0))
-- elementary-number-theory.modular-arithmetic.int-ℤ-Mod
d_int'45'ℤ'45'Mod_64 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_int'45'ℤ'45'Mod_64 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
             (coe
                MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
                (coe v0) (coe v1))
-- elementary-number-theory.modular-arithmetic.is-injective-int-ℤ-Mod
d_is'45'injective'45'int'45'ℤ'45'Mod_74 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'int'45'ℤ'45'Mod_74 = erased
-- elementary-number-theory.modular-arithmetic.is-zero-int-zero-ℤ-Mod
d_is'45'zero'45'int'45'zero'45'ℤ'45'Mod_80 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'int'45'zero'45'ℤ'45'Mod_80 = erased
-- elementary-number-theory.modular-arithmetic.succ-ℤ-Mod
d_succ'45'ℤ'45'Mod_86 :: Integer -> AgdaAny -> AgdaAny
d_succ'45'ℤ'45'Mod_86 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_succ'45'ℤ_130
      _ -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_succ'45'Fin_270
             (coe v0)
-- elementary-number-theory.modular-arithmetic.is-equiv-succ-ℤ-Mod
d_is'45'equiv'45'succ'45'ℤ'45'Mod_92 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'succ'45'ℤ'45'Mod_92 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_is'45'equiv'45'succ'45'ℤ_160
      _ -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_is'45'equiv'45'succ'45'Fin_470
             (coe v0)
-- elementary-number-theory.modular-arithmetic.equiv-succ-ℤ-Mod
d_equiv'45'succ'45'ℤ'45'Mod_98 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'succ'45'ℤ'45'Mod_98 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_succ'45'ℤ'45'Mod_86 (coe v0))
      (coe d_is'45'equiv'45'succ'45'ℤ'45'Mod_92 (coe v0))
-- elementary-number-theory.modular-arithmetic.pred-ℤ-Mod
d_pred'45'ℤ'45'Mod_106 :: Integer -> AgdaAny -> AgdaAny
d_pred'45'ℤ'45'Mod_106 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_pred'45'ℤ_136
      _ -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_pred'45'Fin_414
             (coe v0)
-- elementary-number-theory.modular-arithmetic.issec-pred-ℤ-Mod
d_issec'45'pred'45'ℤ'45'Mod_114 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'pred'45'ℤ'45'Mod_114 = erased
-- elementary-number-theory.modular-arithmetic.isretr-pred-ℤ-Mod
d_isretr'45'pred'45'ℤ'45'Mod_122 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'pred'45'ℤ'45'Mod_122 = erased
-- elementary-number-theory.modular-arithmetic.is-equiv-pred-ℤ-Mod
d_is'45'equiv'45'pred'45'ℤ'45'Mod_128 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'pred'45'ℤ'45'Mod_128 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_is'45'equiv'45'pred'45'ℤ_164
      _ -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_is'45'equiv'45'pred'45'Fin_478
             (coe v0)
-- elementary-number-theory.modular-arithmetic.equiv-pred-ℤ-Mod
d_equiv'45'pred'45'ℤ'45'Mod_134 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'pred'45'ℤ'45'Mod_134 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_pred'45'ℤ'45'Mod_106 (coe v0))
      (coe d_is'45'equiv'45'pred'45'ℤ'45'Mod_128 (coe v0))
-- elementary-number-theory.modular-arithmetic.add-ℤ-Mod
d_add'45'ℤ'45'Mod_142 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_add'45'ℤ'45'Mod_142 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45Zintegers.d_add'45'ℤ_4
      _ -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_add'45'Fin_122
             (coe v0)
-- elementary-number-theory.modular-arithmetic.add-ℤ-Mod'
d_add'45'ℤ'45'Mod''_148 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_add'45'ℤ'45'Mod''_148 v0 v1 v2
  = coe d_add'45'ℤ'45'Mod_142 v0 v2 v1
-- elementary-number-theory.modular-arithmetic.ap-add-ℤ-Mod
d_ap'45'add'45'ℤ'45'Mod_166 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'add'45'ℤ'45'Mod_166 = erased
-- elementary-number-theory.modular-arithmetic.is-equiv-add-ℤ-Mod
d_is'45'equiv'45'add'45'ℤ'45'Mod_178 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'add'45'ℤ'45'Mod_178 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45Zintegers.d_is'45'equiv'45'add'45'ℤ_448
      _ -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_is'45'equiv'45'add'45'Fin_526
             (coe v0)
-- elementary-number-theory.modular-arithmetic.equiv-add-ℤ-Mod
d_equiv'45'add'45'ℤ'45'Mod_186 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'add'45'ℤ'45'Mod_186 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_add'45'ℤ'45'Mod_142 v0 v1)
      (coe d_is'45'equiv'45'add'45'ℤ'45'Mod_178 v0 v1)
-- elementary-number-theory.modular-arithmetic.is-equiv-add-ℤ-Mod'
d_is'45'equiv'45'add'45'ℤ'45'Mod''_200 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'add'45'ℤ'45'Mod''_200 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45Zintegers.d_is'45'equiv'45'add'45'ℤ''_470
      _ -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_is'45'equiv'45'add'45'Fin''_578
             (coe v0)
-- elementary-number-theory.modular-arithmetic.equiv-add-ℤ-Mod'
d_equiv'45'add'45'ℤ'45'Mod''_208 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'add'45'ℤ'45'Mod''_208 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_add'45'ℤ'45'Mod''_148 (coe v0) (coe v1))
      (coe d_is'45'equiv'45'add'45'ℤ'45'Mod''_200 v0 v1)
-- elementary-number-theory.modular-arithmetic.is-injective-add-ℤ-Mod
d_is'45'injective'45'add'45'ℤ'45'Mod_222 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'add'45'ℤ'45'Mod_222 = erased
-- elementary-number-theory.modular-arithmetic.is-injective-add-ℤ-Mod'
d_is'45'injective'45'add'45'ℤ'45'Mod''_230 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'add'45'ℤ'45'Mod''_230 = erased
-- elementary-number-theory.modular-arithmetic.neg-ℤ-Mod
d_neg'45'ℤ'45'Mod_236 :: Integer -> AgdaAny -> AgdaAny
d_neg'45'ℤ'45'Mod_236 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
      _ -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_neg'45'Fin_170
             (coe v0)
-- elementary-number-theory.modular-arithmetic.is-equiv-neg-ℤ-Mod
d_is'45'equiv'45'neg'45'ℤ'45'Mod_242 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'neg'45'ℤ'45'Mod_242 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_is'45'equiv'45'neg'45'ℤ_188
      _ -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_is'45'equiv'45'neg'45'Fin_910
             (coe v0)
-- elementary-number-theory.modular-arithmetic.equiv-neg-ℤ-Mod
d_equiv'45'neg'45'ℤ'45'Mod_248 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'neg'45'ℤ'45'Mod_248 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_neg'45'ℤ'45'Mod_236 (coe v0))
      (coe d_is'45'equiv'45'neg'45'ℤ'45'Mod_242 (coe v0))
-- elementary-number-theory.modular-arithmetic.associative-add-ℤ-Mod
d_associative'45'add'45'ℤ'45'Mod_262 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_associative'45'add'45'ℤ'45'Mod_262 = erased
-- elementary-number-theory.modular-arithmetic.commutative-add-ℤ-Mod
d_commutative'45'add'45'ℤ'45'Mod_272 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_commutative'45'add'45'ℤ'45'Mod_272 = erased
-- elementary-number-theory.modular-arithmetic.left-unit-law-add-ℤ-Mod
d_left'45'unit'45'law'45'add'45'ℤ'45'Mod_280 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'unit'45'law'45'add'45'ℤ'45'Mod_280 = erased
-- elementary-number-theory.modular-arithmetic.right-unit-law-add-ℤ-Mod
d_right'45'unit'45'law'45'add'45'ℤ'45'Mod_288 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'unit'45'law'45'add'45'ℤ'45'Mod_288 = erased
-- elementary-number-theory.modular-arithmetic.left-inverse-law-add-ℤ-Mod
d_left'45'inverse'45'law'45'add'45'ℤ'45'Mod_296 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'inverse'45'law'45'add'45'ℤ'45'Mod_296 = erased
-- elementary-number-theory.modular-arithmetic.right-inverse-law-add-ℤ-Mod
d_right'45'inverse'45'law'45'add'45'ℤ'45'Mod_304 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'inverse'45'law'45'add'45'ℤ'45'Mod_304 = erased
-- elementary-number-theory.modular-arithmetic.left-successor-law-add-ℤ-Mod
d_left'45'successor'45'law'45'add'45'ℤ'45'Mod_314 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'successor'45'law'45'add'45'ℤ'45'Mod_314 = erased
-- elementary-number-theory.modular-arithmetic.right-successor-law-add-ℤ-Mod
d_right'45'successor'45'law'45'add'45'ℤ'45'Mod_324 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'successor'45'law'45'add'45'ℤ'45'Mod_324 = erased
-- elementary-number-theory.modular-arithmetic.left-predecessor-law-add-ℤ-Mod
d_left'45'predecessor'45'law'45'add'45'ℤ'45'Mod_334 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'predecessor'45'law'45'add'45'ℤ'45'Mod_334 = erased
-- elementary-number-theory.modular-arithmetic.right-predecessor-law-add-ℤ-Mod
d_right'45'predecessor'45'law'45'add'45'ℤ'45'Mod_344 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'predecessor'45'law'45'add'45'ℤ'45'Mod_344 = erased
-- elementary-number-theory.modular-arithmetic.is-add-one-succ-ℤ-Mod
d_is'45'add'45'one'45'succ'45'ℤ'45'Mod_352 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'one'45'succ'45'ℤ'45'Mod_352 = erased
-- elementary-number-theory.modular-arithmetic.is-add-one-succ-ℤ-Mod'
d_is'45'add'45'one'45'succ'45'ℤ'45'Mod''_360 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'one'45'succ'45'ℤ'45'Mod''_360 = erased
-- elementary-number-theory.modular-arithmetic.is-add-neg-one-pred-ℤ-Mod
d_is'45'add'45'neg'45'one'45'pred'45'ℤ'45'Mod_368 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'neg'45'one'45'pred'45'ℤ'45'Mod_368 = erased
-- elementary-number-theory.modular-arithmetic.is-add-neg-one-pred-ℤ-Mod'
d_is'45'add'45'neg'45'one'45'pred'45'ℤ'45'Mod''_376 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'neg'45'one'45'pred'45'ℤ'45'Mod''_376 = erased
-- elementary-number-theory.modular-arithmetic.mul-ℤ-Mod
d_mul'45'ℤ'45'Mod_382 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_mul'45'ℤ'45'Mod_382 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45Zintegers.d_mul'45'ℤ_4
      _ -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mul'45'Fin_342
             (coe v0)
-- elementary-number-theory.modular-arithmetic.mul-ℤ-Mod'
d_mul'45'ℤ'45'Mod''_388 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_mul'45'ℤ'45'Mod''_388 v0 v1 v2
  = coe d_mul'45'ℤ'45'Mod_382 v0 v2 v1
-- elementary-number-theory.modular-arithmetic.ap-mul-ℤ-Mod
d_ap'45'mul'45'ℤ'45'Mod_406 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'mul'45'ℤ'45'Mod_406 = erased
-- elementary-number-theory.modular-arithmetic.associative-mul-ℤ-Mod
d_associative'45'mul'45'ℤ'45'Mod_422 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_associative'45'mul'45'ℤ'45'Mod_422 = erased
-- elementary-number-theory.modular-arithmetic.commutative-mul-ℤ-Mod
d_commutative'45'mul'45'ℤ'45'Mod_432 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_commutative'45'mul'45'ℤ'45'Mod_432 = erased
-- elementary-number-theory.modular-arithmetic.left-unit-law-mul-ℤ-Mod
d_left'45'unit'45'law'45'mul'45'ℤ'45'Mod_440 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'unit'45'law'45'mul'45'ℤ'45'Mod_440 = erased
-- elementary-number-theory.modular-arithmetic.right-unit-law-mul-ℤ-Mod
d_right'45'unit'45'law'45'mul'45'ℤ'45'Mod_448 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'unit'45'law'45'mul'45'ℤ'45'Mod_448 = erased
-- elementary-number-theory.modular-arithmetic.left-distributive-mul-add-ℤ-Mod
d_left'45'distributive'45'mul'45'add'45'ℤ'45'Mod_460 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'distributive'45'mul'45'add'45'ℤ'45'Mod_460 = erased
-- elementary-number-theory.modular-arithmetic.right-distributive-mul-add-ℤ-Mod
d_right'45'distributive'45'mul'45'add'45'ℤ'45'Mod_472 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'distributive'45'mul'45'add'45'ℤ'45'Mod_472 = erased
-- elementary-number-theory.modular-arithmetic.is-mul-neg-one-neg-ℤ-Mod
d_is'45'mul'45'neg'45'one'45'neg'45'ℤ'45'Mod_480 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'mul'45'neg'45'one'45'neg'45'ℤ'45'Mod_480 = erased
-- elementary-number-theory.modular-arithmetic.is-mul-neg-one-neg-ℤ-Mod'
d_is'45'mul'45'neg'45'one'45'neg'45'ℤ'45'Mod''_488 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'mul'45'neg'45'one'45'neg'45'ℤ'45'Mod''_488 = erased
-- elementary-number-theory.modular-arithmetic.mod-ℕ
d_mod'45'ℕ_494 :: Integer -> Integer -> AgdaAny
d_mod'45'ℕ_494 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_int'45'ℕ_36
             (coe v1)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mod'45'succ'45'ℕ_6
             (coe v2) (coe v1)
-- elementary-number-theory.modular-arithmetic.mod-ℤ
d_mod'45'ℤ_504 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 -> AgdaAny
d_mod'45'ℤ_504 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_neg'45'Fin_170
                    (coe v0)
                    (coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mod'45'succ'45'ℕ_6
                       (coe v2) (coe addInt (coe (1 :: Integer)) (coe v3)))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v3 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
                      -> coe
                           MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_zero'45'Fin_230
                           (coe v2)
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
                      -> coe
                           MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mod'45'succ'45'ℕ_6
                           (coe v2) (coe addInt (coe (1 :: Integer)) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.modular-arithmetic.mod-zero-ℕ
d_mod'45'zero'45'ℕ_522 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_mod'45'zero'45'ℕ_522 = erased
-- elementary-number-theory.modular-arithmetic.preserves-successor-mod-ℕ
d_preserves'45'successor'45'mod'45'ℕ_530 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_preserves'45'successor'45'mod'45'ℕ_530 = erased
-- elementary-number-theory.modular-arithmetic.mod-zero-ℤ
d_mod'45'zero'45'ℤ_540 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_mod'45'zero'45'ℤ_540 = erased
-- elementary-number-theory.modular-arithmetic.mod-one-ℤ
d_mod'45'one'45'ℤ_546 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_mod'45'one'45'ℤ_546 = erased
-- elementary-number-theory.modular-arithmetic.mod-neg-one-ℤ
d_mod'45'neg'45'one'45'ℤ_552 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_mod'45'neg'45'one'45'ℤ_552 = erased
-- elementary-number-theory.modular-arithmetic.preserves-successor-mod-ℤ
d_preserves'45'successor'45'mod'45'ℤ_560 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_preserves'45'successor'45'mod'45'ℤ_560 = erased
-- elementary-number-theory.modular-arithmetic.preserves-predecessor-mod-ℤ
d_preserves'45'predecessor'45'mod'45'ℤ_580 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_preserves'45'predecessor'45'mod'45'ℤ_580 = erased
-- elementary-number-theory.modular-arithmetic.preserves-add-mod-ℤ
d_preserves'45'add'45'mod'45'ℤ_602 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_preserves'45'add'45'mod'45'ℤ_602 = erased
-- elementary-number-theory.modular-arithmetic.preserves-neg-mod-ℤ
d_preserves'45'neg'45'mod'45'ℤ_636 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_preserves'45'neg'45'mod'45'ℤ_636 = erased
-- elementary-number-theory.modular-arithmetic.preserves-mul-mod-ℤ
d_preserves'45'mul'45'mod'45'ℤ_650 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_preserves'45'mul'45'mod'45'ℤ_650 = erased
-- elementary-number-theory.modular-arithmetic.cong-int-mod-ℕ
d_cong'45'int'45'mod'45'ℕ_684 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'int'45'mod'45'ℕ_684 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.du_refl'45'cong'45'ℤ_140
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.d_cong'45'int'45'cong'45'ℕ_388
             (coe v0)
             (coe
                MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
                (coe v0)
                (coe
                   MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mod'45'succ'45'ℕ_6
                   (coe v2) (coe v1)))
             (coe v1)
             (coe
                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_cong'45'nat'45'mod'45'succ'45'ℕ_34
                (coe v2) (coe v1))
-- elementary-number-theory.modular-arithmetic.cong-int-mod-ℤ
d_cong'45'int'45'mod'45'ℤ_696 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'int'45'mod'45'ℤ_696 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.du_refl'45'cong'45'ℤ_140
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3
               -> coe
                    MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.du_transitive'45'cong'45'ℤ_186
                    (coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.d_cong'45'int'45'cong'45'ℕ_388
                       (coe v0)
                       (coe
                          MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
                          (coe v0)
                          (coe
                             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mul'45'Fin_342
                             (coe v0)
                             (coe
                                MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.du_neg'45'one'45'Fin_24)
                             (coe
                                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mod'45'succ'45'ℕ_6
                                (coe v2) (coe addInt (coe (1 :: Integer)) (coe v3)))))
                       (coe
                          MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
                          (coe v2)
                          (coe
                             MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
                             (coe v0)
                             (coe
                                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mod'45'succ'45'ℕ_6
                                (coe v2) (coe addInt (coe (1 :: Integer)) (coe v3)))))
                       (coe
                          MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_cong'45'mul'45'Fin_382
                          (coe v0)
                          (coe
                             MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.du_neg'45'one'45'Fin_24)
                          (coe
                             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mod'45'succ'45'ℕ_6
                             (coe v2) (coe addInt (coe (1 :: Integer)) (coe v3)))))
                    (coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.du_transitive'45'cong'45'ℤ_186
                       (coe
                          MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.d_cong'45'int'45'cong'45'ℕ_388
                          (coe v0)
                          (coe
                             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
                             (coe v2)
                             (coe
                                MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
                                (coe v0)
                                (coe
                                   MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mod'45'succ'45'ℕ_6
                                   (coe v2) (coe addInt (coe (1 :: Integer)) (coe v3)))))
                          (coe
                             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
                             (coe v2) (coe addInt (coe (1 :: Integer)) (coe v3)))
                          (coe
                             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers.d_congruence'45'mul'45'ℕ_422
                             (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
                                (coe v0)
                                (coe
                                   MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mod'45'succ'45'ℕ_6
                                   (coe v2) (coe addInt (coe (1 :: Integer)) (coe v3))))
                             (coe v2) (coe addInt (coe (1 :: Integer)) (coe v3))
                             (coe
                                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers.du_refl'45'cong'45'ℕ_100)
                             (coe
                                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_cong'45'nat'45'mod'45'succ'45'ℕ_34
                                (coe v2) (coe addInt (coe (1 :: Integer)) (coe v3)))))
                       (coe
                          MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                          (coe
                             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                             (coe
                                MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v3)))
                          erased))
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v3 of
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v4
                      -> coe
                           MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.d_cong'45'int'45'cong'45'ℕ_388
                           (coe v0)
                           (coe
                              MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
                              (coe v0)
                              (coe
                                 MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mod'45'succ'45'ℕ_6
                                 (coe v2) (coe (0 :: Integer))))
                           (coe (0 :: Integer))
                           (coe
                              MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_cong'45'nat'45'mod'45'succ'45'ℕ_34
                              (coe v2) (coe (0 :: Integer)))
                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v4
                      -> coe
                           MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.d_cong'45'int'45'cong'45'ℕ_388
                           (coe v0)
                           (coe
                              MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
                              (coe v0)
                              (coe
                                 MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_mod'45'succ'45'ℕ_6
                                 (coe v2) (coe addInt (coe (1 :: Integer)) (coe v4))))
                           (coe addInt (coe (1 :: Integer)) (coe v4))
                           (coe
                              MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes.d_cong'45'nat'45'mod'45'succ'45'ℕ_34
                              (coe v2) (coe addInt (coe (1 :: Integer)) (coe v4)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.modular-arithmetic.cong-eq-mod-ℤ
d_cong'45'eq'45'mod'45'ℤ_716 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'eq'45'mod'45'ℤ_716 v0 v1 v2 ~v3
  = du_cong'45'eq'45'mod'45'ℤ_716 v0 v1 v2
du_cong'45'eq'45'mod'45'ℤ_716 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_cong'45'eq'45'mod'45'ℤ_716 v0 v1 v2
  = coe
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.du_concatenate'45'cong'45'eq'45'cong'45'ℤ_284
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.du_symmetric'45'cong'45'ℤ_156
         (coe d_cong'45'int'45'mod'45'ℤ_696 (coe v0) (coe v1)))
      (coe d_cong'45'int'45'mod'45'ℤ_696 (coe v0) (coe v2))
-- elementary-number-theory.modular-arithmetic.eq-cong-int-ℤ-Mod
d_eq'45'cong'45'int'45'ℤ'45'Mod_732 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'cong'45'int'45'ℤ'45'Mod_732 = erased
-- elementary-number-theory.modular-arithmetic.eq-mod-cong-ℤ
d_eq'45'mod'45'cong'45'ℤ_748 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'mod'45'cong'45'ℤ_748 = erased
-- elementary-number-theory.modular-arithmetic.is-zero-mod-div-ℤ
d_is'45'zero'45'mod'45'div'45'ℤ_762 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'mod'45'div'45'ℤ_762 = erased
-- elementary-number-theory.modular-arithmetic.div-is-zero-mod-ℤ
d_div'45'is'45'zero'45'mod'45'ℤ_778 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'is'45'zero'45'mod'45'ℤ_778 v0 v1 ~v2
  = du_div'45'is'45'zero'45'mod'45'ℤ_778 v0 v1
du_div'45'is'45'zero'45'mod'45'ℤ_778 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'is'45'zero'45'mod'45'ℤ_778 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45Zintegers.du_refl'45'div'45'ℤ_14
      _ -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45Zintegers.du_div'45'is'45'cong'45'zero'45'ℤ_44
             (coe
                du_cong'45'eq'45'mod'45'ℤ_716 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_zero'45'ℤ_16))
-- elementary-number-theory.modular-arithmetic.issec-int-ℤ-Mod
d_issec'45'int'45'ℤ'45'Mod_790 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'int'45'ℤ'45'Mod_790 = erased
-- elementary-number-theory.modular-arithmetic.is-one-is-fixed-point-succ-ℤ-Mod
d_is'45'one'45'is'45'fixed'45'point'45'succ'45'ℤ'45'Mod_800 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'is'45'fixed'45'point'45'succ'45'ℤ'45'Mod_800
  = erased
-- elementary-number-theory.modular-arithmetic.has-no-fixed-points-succ-ℤ-Mod
d_has'45'no'45'fixed'45'points'45'succ'45'ℤ'45'Mod_812 ::
  Integer ->
  AgdaAny ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_has'45'no'45'fixed'45'points'45'succ'45'ℤ'45'Mod_812 = erased
-- elementary-number-theory.modular-arithmetic.has-no-fixed-points-succ-Fin
d_has'45'no'45'fixed'45'points'45'succ'45'Fin_822 ::
  Integer ->
  AgdaAny ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_has'45'no'45'fixed'45'points'45'succ'45'Fin_822 = erased
