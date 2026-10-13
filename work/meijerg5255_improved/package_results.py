"""Save metadata and bundle the complete reproducible arithmetic update."""
from pathlib import Path
import json, shutil, zipfile, sys
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/meijerg5255_improved'
WORK=Path(__file__).resolve().parent
sys.set_int_max_str_digits(0)
rates=json.loads((ROOT/'results/meijerg5255_arithmetic/rates/spectral_rates.json').read_text())
meta=dict(status='STRONG_NUMERICAL_CANDIDATE',
    scope='Arithmetic update to the existing trajectory; not a new or optimized numerical trajectory.',
    family='MeijerG',family_parameters=[5,2,5,5,1],p=5,q=5,z=1,
    initial_point=[1,1,0,0,0,0,0,0,0,0],
    direction=[16,17,-11,-12,-10,2,1,0,-1,-2],orientation='forward',
    dimension=4,selected_column=0,steps='n=N-1',
    initial_condition_rows=[['0','0','-6*A','3*A-2*B'],['12','0','0','0']],
    target='A*zeta(3)+B*zeta(4), fixed integer or rational pair not (0,0)',
    product_gauge='Native CMF, no scalar gauge',
    asymptotic_gauge=rates['leading_gauge'],
    limiting_characteristic_coefficients=rates['characteristic_coefficients'],
    limiting_characteristic_roots=rates['roots'],
    source='User-specified trajectory and accepted initial conditions; existing readout reproduction retained in bundle.',
    measured_delta_depths=[1000,2000,4000,8000],
    exact_gcd_depths=[50,100,250,500,1000,2000,4000,8000],
    delta_data='residuals/delta_summary.json',
    all_precisions='residuals/delta_N*.json',
    arithmetic_certificate='residuals/final_bound_certificate.json',
    accepted_analytic_inputs=dict(raw_log_growth='53.287583322620205267...',
                                  ratio_error_exponent='112.807539247454680339...'),
    improved_delta_lower=dict(pure_zeta3='0.22626234',joint='0.01634832'),
    deduplication='Same candidate, trajectory, orientation, and rows as prior MeijerG readout. Only the arithmetic certificate improves.')
(OUT/'experiment.json').write_text(json.dumps(meta,indent=2)+'\n')
shutil.copy2(WORK/'arithmetic/second_order_trace.tex',OUT/'arithmetic/second_order_trace.tex')
archive=ROOT/'results/meijerg_zeta3_zeta4_improved_bundle.zip'
directories=['work/meijerg5255_arithmetic','results/meijerg5255_arithmetic',
             'work/meijerg5255_improved','results/meijerg5255_improved',
             'work/meijerg5255_z3_z4_readout','results/meijerg5255_z3_z4_readout']
files=[]
for directory in directories:
    for p in (ROOT/directory).rglob('*'):
        if not p.is_file() or '__pycache__' in p.parts or 'pdf_qa' in p.parts:continue
        if p.suffix.lower() not in ('.py','.json','.tex','.txt','.csv','.pdf','.md'):continue
        files.append(p)
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for p in sorted(set(files)):z.write(p,p.relative_to(ROOT))
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    count=len(z.namelist())
print(json.dumps(dict(bundle=str(archive),file_count=count,bytes=archive.stat().st_size)))
