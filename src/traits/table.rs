use ff::PrimeField;
use crate::traits::Group;
trait ConstraintSystem{

}
struct Table<F: PrimeField, G: Group, const ROW_NUM: usize, const COLUMN_NUM: usize>{
    // constraint system between columns
    cs:dyn ConstraintSystem,
    // table assignment
    cells:[[F;ROW_NUM]; COLUMN_NUM],
    column_polys: [Polynomial<F,ROW_NUM>;COLUMN_NUM],
    column_poly_commitments: [G;COLUMN_NUM],
}

struct Cell<F:PrimeField>{
    column_index: usize,
    row_index: usize,
    value: F,
}

impl <F: PrimeField, G: Group, const ROW_NUM: usize, const COLUMN_NUM: usize> Table<F,G,ROW_NUM,COLUMN_NUM>{
    fn new(cs_instance: impl ConstraintSystem)->Self{
        Self{
            cs:cs_instance,
            cells: [[F::ZERO;ROW_NUM];COLUMN_NUM],
            column_polys: std::array::from_fn(|i| Polynomial::empty()),
            column_poly_commitments: std::array::from_fn(||),
        }
    }

    fn assign_row(&self,row_index: usize, values: [F;COLUMN_NUM]){
        values.iter().enumerate().for_each(|column_index,value|{
            self.cells[column_index][row_index] = value;
        })
    }

    fn compute_column_polynomial(&mut self,column_index:usize){
        let roots = [F::ZERO;COLUMN_NUM];
        self.column_polys[column_index] = Polynomial::<F,ROW_NUM>::FFT(roots,self.cells[column_index]);
    }

    fn commit_column_polynomial<G:Group>(poly: &Polynomial<F,ROW_NUM>,setup:[G;ROW_NUM]) -> G{
        poly.commit_poly(setup)
    }


}


enum PolynomialType{
    Evaluation,
    Coefficient,
    Empty,
}
pub struct Polynomial<F: PrimeField,const VALUES_NUM: usize>{
    values: [F;VALUES_NUM],
    form_type:PolynomialType,
}

impl <F: PrimeField,const VALUES_NUM: usize> Polynomial<F,VALUES_NUM>{
    fn empty() -> Polynomial<F,VALUES_NUM>{
        Self{
            values: [F::ZERO;VALUES_NUM],
            form_type: PolynomialType::Empty,
        }
    }
    fn degree(&self) -> usize{
        VALUES_NUM-1
    }

    fn eq_degree<const Other_Degree: usize> (&self,other:&Polynomial<F,Other_Degree>) -> bool {
        self.degree() == other.degree()
    }

    fn interpolate(x: [F;VALUES_NUM] , y: [F;VALUES_NUM]) -> Self{
        Self{
            values:y,
            form_type:PolynomialType::Coefficient
        }
    }

    fn FFT(x: [F;VALUES_NUM] , y: [F;VALUES_NUM]) -> Self{
        Self{
            values:y,
            form_type:PolynomialType::Evaluation
        }
    }

    fn commit_poly<G:Group>(&self,setup:[G;VALUES_NUM])-> G{
        setup[0]
    }

}