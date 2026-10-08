from pathlib import Path
from fractions import Fraction as F
import ast,hashlib,json,re,unittest
ROOT=Path(__file__).resolve().parent
class PackageChecks(unittest.TestCase):
 def test_source_integrity(self):
  m=json.loads((ROOT/'SOURCE_MANIFEST.json').read_text())
  for x in m['source_files']:
   b=(ROOT/x['published_path']).read_bytes();self.assertEqual(hashlib.sha256(b).hexdigest(),x['published_sha256']);self.assertEqual(len(b),x['published_bytes'])
 def test_exact_selected_witness(self):
  d=json.loads((ROOT/'ASSEMBLY_CERTIFICATE.json').read_text());p=d['balanced_geometry']['parameters']
  self.assertEqual(F(p['kappa']),F(1228547206,10**14));self.assertEqual(F(d['bit']['a']),F(12285623,10**12))
  self.assertGreater(F(d['balanced_geometry']['absorption_gap']),0)
  self.assertEqual(d['product_rows']['degree'],96000)
 def test_static_source_and_math(self):
  for p in ROOT.rglob('*.py'):ast.parse(p.read_text(),filename=str(p))
  for p in ROOT.rglob('*.md'):
   s=p.read_text();self.assertEqual(s.count('$$')%2,0);self.assertFalse(any(ord(c)<32 and c not in '\n\t\r' for c in s))
   for u in re.findall(r'\]\(([^)]+)\)',s):
    if '://' in u or u.startswith('#'):continue
    self.assertTrue((p.parent/u.split('#')[0]).exists(),str((p,u)))
if __name__=='__main__':unittest.main()
