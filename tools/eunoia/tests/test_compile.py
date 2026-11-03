"""Generator regressions. Run from any directory with Python's unittest."""
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("eunoia_compiler", ROOT / "tools/eunoia/compile.py")
eoc = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = eoc
SPEC.loader.exec_module(eoc)

INITIAL = ROOT / "tools/eunoia/signatures/cpc/Cpc.eo"
RULES = (ROOT / "tools/eunoia/rules.txt").read_text().split()
BASE = '(declare-const not (-> Bool Bool))\n'
RULE = '(declare-rule brand_new ((F Bool)) :args (F) :conclusion F)\n'


class CompileTests(unittest.TestCase):
    def compile_text(self, text, rules=("brand_new",)):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Sig.eo"
            path.write_text(text)
            return eoc.Compiler(path).compile(rules)

    def reject(self, text, message):
        with self.assertRaisesRegex(eoc.SignatureError, message):
            self.compile_text(text)

    def test_snapshot_regenerates_exactly(self):
        code, manifest = eoc.Compiler(INITIAL).compile(RULES)
        self.assertEqual(code, (ROOT / "theories/checker/eunoia/CpcGenerated.v").read_text())
        self.assertEqual(len(manifest["excluded_rules"]), 582)
        self.assertEqual(len(manifest["sources"]), 35)
        self.assertIn("$mk_cong_rhs", manifest["programs"])
        self.assertIn("$run_evaluate", manifest["programs"])
        self.assertIn("$is_aci_norm", manifest["expanded_definitions"])

    def test_repeatable_selection_order_independent(self):
        self.assertEqual(eoc.Compiler(INITIAL).compile(RULES),
                         eoc.Compiler(INITIAL).compile(list(reversed(RULES))))

    def test_manifest_matches_pinned_source_and_fixture_bytes(self):
        import hashlib, json
        manifest = json.loads((ROOT / 'tools/eunoia/cpc-manifest.json').read_text())
        for source, digest in manifest['sources'].items():
            self.assertEqual(hashlib.sha256((INITIAL.parent / source).read_bytes()).hexdigest(), digest)
        fixtures = ROOT / 'tools/eunoia/tests/fixtures'
        provenance = json.loads((fixtures / 'provenance.json').read_text())
        for name, data in provenance.items():
            self.assertEqual(data['exit_code'], 0)
            self.assertEqual(hashlib.sha256((ROOT / data['input']).read_bytes()).hexdigest(), data['input_sha256'])
            self.assertEqual(hashlib.sha256((fixtures / (name + '.cpc')).read_bytes()).hexdigest(), data['proof_sha256'])
        self.assertEqual((fixtures / 'uf4.cpc').read_bytes(),
                         (ROOT / 'unit-tests/eunoia-fixtures/default/uf4.cpc').read_bytes())

    def test_generic_premise_operator_is_emitted_without_constructor_use(self):
        text = '(declare-const both (-> Bool Bool Bool) :right-assoc-nil true)\n' + RULE.replace(':args (F)', ':premise-list F both')
        code, _ = self.compile_text(text)
        self.assertIn('("both", Symbol "true")', code)

    def test_novel_rule_and_changed_conclusion(self):
        a, _ = self.compile_text(BASE + RULE)
        b, _ = self.compile_text(BASE + RULE.replace(':conclusion F', ':conclusion (not F)'))
        self.assertNotEqual(a, b)
        self.assertIn('"brand_new"', a)
        self.assertIn('EApply', b)

    def test_changed_helper_body_affects_executable_data(self):
        sig = ('(program $f ((F Bool)) :signature (Bool) Bool ((($f F) F)))\n'
               + RULE.replace(':conclusion F', ':conclusion ($f F)'))
        a, _ = self.compile_text(sig)
        b, _ = self.compile_text(sig.replace('(($f F) F)', '(($f F) true)'))
        self.assertNotEqual(a, b)
        self.assertIn('case_body := (ESymbol "true")', b)

    def test_changed_requirement_affects_executable_data(self):
        a, _ = self.compile_text(RULE.replace(':conclusion', ':requires (((eo::eq F F) true)) :conclusion'))
        b, _ = self.compile_text(RULE.replace(':conclusion', ':requires (((eo::eq F F) false)) :conclusion'))
        self.assertNotEqual(a, b)
        self.assertIn('rule_requires := [', a)

    def test_reject_malformed(self):
        for text in ['(', ')', '(declare-rule)', '(include "unterminated)', '(())']:
            with self.subTest(text=text), self.assertRaises(eoc.SignatureError):
                self.compile_text(text)

    def test_reject_unsupported_rule_constructs(self):
        for field in [':sorry', ':conclusion-explicit F']:
            with self.subTest(field=field):
                self.reject(RULE.replace(':args (F)', field), 'unsupported')

    def test_assumption_is_source_generated(self):
        code, manifest = self.compile_text(RULE.replace(':args (F)', ':assumption F'))
        self.assertIn('rule_assumption := (Some (PVar 0))', code)
        self.assertEqual(manifest['assumption_rules'], ['brand_new'])
        changed, _ = self.compile_text(BASE + RULE.replace(':args (F)', ':assumption (not F)'))
        self.assertIn('rule_assumption := (Some (PApply', changed)
        self.assertNotEqual(code, changed)

    def test_binders_and_function_types(self):
        self.reject(RULE.replace('(F Bool)', '(F Bool :mystery)'), 'unsupported binder')
        code, _ = self.compile_text(RULE.replace('(F Bool)', '(F (-> Bool Bool))'))
        self.assertIn('PSymbol "->"', code)
        self.reject(RULE.replace('(F Bool)', '(F Unknown)'), 'unsupported atomic type')

    def test_reject_native_and_unknown_calls(self):
        for call in ['(eo::unimplemented F)', '(undefined F)']:
            with self.subTest(call=call):
                self.reject(RULE.replace(':conclusion F', ':conclusion ' + call), 'unsupported|unknown')

    def test_reject_helper_dependency(self):
        sig = ('(program $f ((F Bool)) :signature (Bool) Bool ((($f F) (eo::mystery F))))\n'
               + RULE.replace(':conclusion F', ':conclusion ($f F)'))
        self.reject(sig, 'unsupported native operation')

    def test_define_helper_expands(self):
        code, manifest = self.compile_text('(define $f ((F Bool)) (not F))\n' + BASE +
                      RULE.replace(':conclusion F', ':conclusion ($f F)'))
        self.assertIn('$f', manifest['expanded_definitions'])
        self.assertIn('ESymbol "not"', code)
        self.assertNotIn('ECall "$f"', code)

    def test_nil_variadic_metadata_and_list_binder(self):
        code, _ = self.compile_text('(declare-const and (-> Bool Bool Bool) :right-assoc-nil true)\n'
                    + RULE.replace('(F Bool)', '(F Bool :list)').replace(':conclusion F', ':conclusion (and F F)'))
        self.assertIn('("and", Symbol "true")', code)

    def test_overloaded_constructor_shapes_preserved(self):
        code, _ = self.compile_text(BASE + '(declare-const not (-> Bool Bool Bool))\n'
                    + RULE.replace(':conclusion F', ':conclusion (not F)'))
        self.assertIn('EApply (ESymbol "not")', code)

    def test_prototypes_and_conflicts(self):
        proto = '(program $f () :signature (Bool) Bool)\n'
        body = '(program $f ((F Bool)) :signature (Bool) Bool ((($f F) F)))\n'
        rule = RULE.replace(':conclusion F', ':conclusion ($f F)')
        a, _ = self.compile_text(proto + body + rule)
        b, _ = self.compile_text(body + proto + rule)
        self.assertEqual(a, b)
        self.reject(proto.replace(':signature (Bool) Bool', ':signature (Type) Bool') + body + rule,
                    'conflicting prototype')

    def test_reject_bad_constructor_arity(self):
        self.reject(BASE + RULE.replace(':conclusion F', ':conclusion (not F F)'), 'exactly 1 arguments')

    def test_shadowing_and_parallel_let(self):
        code, _ = self.compile_text(RULE.replace(':conclusion F', ':conclusion (eo::define ((F true)) F)'))
        self.assertIn('rule_conclusion := (ESymbol "true")', code)
        code, _ = self.compile_text(RULE.replace(':conclusion F', ':conclusion (eo::define ((x F) (y true)) x)'))
        self.assertIn('rule_conclusion := (EVar 0)', code)
        self.reject(RULE.replace(':conclusion F', ':conclusion (eo::define ((x F) (y x)) y)'), 'unknown symbol x')

    def test_definition_fresh_names_cannot_capture_actual_arguments(self):
        source = '(define $f ((F Bool)) (eo::define ((x true)) F))\n' + RULE.replace('(F Bool)', '($eoc.local.1 Bool)').replace(':args (F)', ':args ($eoc.local.1)').replace(':conclusion F', ':conclusion ($f $eoc.local.1)')
        code, _ = self.compile_text(source)
        self.assertIn('rule_conclusion := (EVar 0)', code)

    def test_duplicate_and_missing_fields(self):
        self.reject(RULE.replace(':args (F)', ':args (F) :args (F)'), 'duplicate rule field')
        self.reject(RULE.replace(':conclusion F', ''), 'missing :conclusion')

    def test_includes_once_and_cycles(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'A.eo').write_text(RULE)
            (root / 'B.eo').write_text('(include "A.eo")\n(include "A.eo")')
            code, manifest = eoc.Compiler(root / 'B.eo').compile(['brand_new'])
            self.assertEqual(len(manifest['sources']), 2)
            self.assertIn('"brand_new"', code)
            (root / 'A.eo').write_text('(include "B.eo")')
            with self.assertRaisesRegex(eoc.SignatureError, 'include cycle'):
                eoc.Compiler(root / 'B.eo')

    def test_lexer_preserves_semicolon_and_doubled_quote_in_include(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'a;"b.eo').write_text(RULE)
            (root / 'root.eo').write_text(';comment\n(include "a;""b.eo") ; comment')
            self.assertEqual(eoc.Compiler(root / 'root.eo').compile(['brand_new'])[1]['selected_rules'], ['brand_new'])

    def test_cli_failure_leaves_outputs_untouched(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'Bad.eo').write_text(RULE.replace(':conclusion F', ':conclusion (eo::bad F)'))
            (root / 'out.v').write_text('sentinel')
            proc = subprocess.run([sys.executable, str(ROOT / 'tools/eunoia/compile.py'), str(root / 'Bad.eo'),
                                   '--rules', 'brand_new', '--output', str(root / 'out.v'),
                                   '--manifest', str(root / 'out.json')], capture_output=True, text=True)
            self.assertEqual(proc.returncode, 2)
            self.assertIn('Bad.eo:1: unsupported native operation', proc.stderr)
            self.assertEqual((root / 'out.v').read_text(), 'sentinel')
            self.assertFalse((root / 'out.json').exists())


if __name__ == '__main__':
    unittest.main()
