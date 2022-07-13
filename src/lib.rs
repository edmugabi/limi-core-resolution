use std::ops::{Index, RangeFrom};

pub trait PrettyPrint {
    fn pretty_print(&self) -> String;
}

pub trait Unify<Head, Env> {
    type Err;
    fn unify(&self, other: &Head, env: &mut Env) -> Result<(), Self::Err>;
}

pub trait Rewriting
{
    type Head;
    type Res: Unify<Self::Head, Self::Env>;
    type Env;
    fn subst(&self, env: &Self::Env) -> Self::Res;
}

pub trait EnvTrait {
    fn empty() -> Self;
    fn compose(self,other: &Self) -> Self;
}

pub trait Rename {
    fn rename(&mut self, index: usize);
}

pub enum Strategy {
    DFS,
    BFS,
    DLS(usize)
}

pub struct CPoint<Goals, Env>
{
    goals: Goals,
    env: Env,
    clause_range: RangeFrom<usize>,
    depth: usize,
}

impl<Goals, Env> CPoint<Goals, Env>
{
    fn new(goals: Goals, env: Env) -> Self {
        Self {
            goals,
            env,
            clause_range: 0..,
            depth: 1
        }
    }
}

pub enum Soln<Goals, Env>
{
    CPoints([CPoint<Goals, Env>;2]),
    Res(Env),
    NoRule
}

pub trait DBTrait
 where
    Self: Extend<(Self::Goals, Self::Head)>
{
    type Goals;
    type Head;

    fn resolve_one_step<'a, Goal, Env>(
        &'a self,
        goal: &Goal,
        env:  &Env,
        clause_range: RangeFrom<usize>,
        // uses the depth as renaming index
        renaming_index: usize
    )
    -> Option<(Self::Goals, Env, RangeFrom<usize>)>
    where
        Self::Head: Rename + Clone,
        Env: EnvTrait,
        Goal: Rewriting<Head=Self::Head, Env=Env>,
        Self::Goals: Rename + Extend<Goal> + Clone,
        Self: Index<RangeFrom<usize>, Output=[(Self::Goals, Self::Head)]>,
    {

        let range = clause_range.clone();
        for (i, (body, head)) in self[range].iter().enumerate()
        {

            head.clone().rename(renaming_index);
            let goal = goal.subst(env);
    
            let mut new_env = Env::empty();
            match goal.unify(&head, &mut new_env) {
                Ok(()) => {
                    //println!("\n\n{:?}", goal);
                    //println!("{:?}", &args.clauses.as_slice()[i]);
                    let ret_env = new_env.compose(env);
                    let clause_range = (clause_range.start+i+1)..;

                    // an optimisation where the body is renamed only when necessary
                    let mut new_body: Self::Goals = body.clone();
                    new_body.rename(renaming_index);
    
                    return Some((new_body, ret_env, clause_range))    
                }
                Err(_) => continue
            }
            
        }
        //println!("\n\nUnsolved Goal: {:?}", self.subst(&args.env));
        None
    }
    
    fn resolve<Goal, Env>(
        &self,
        cpoint: CPoint<Self::Goals, Env>
    ) -> Soln<Self::Goals, Env>
        where
        Self::Head: Rename + Clone,
        Env: EnvTrait,
        Goal: Rewriting<Head=Self::Head, Env=Env>,
        Self::Goals: Rename + Extend<Goal> + Clone,
        Self: Index<RangeFrom<usize>, Output=[(Self::Goals, Self::Head)]>,

        Goal: Clone,
        for<'b> &'b Self::Goals: IntoIterator<Item=&'b Goal>
    {
        let mut goals_iter = (&cpoint.goals).into_iter();

        match goals_iter.next() {
            Some(goal_ref) => {

                let some_res = self.resolve_one_step(
                    goal_ref,
                    &cpoint.env,
                    cpoint.clause_range.clone(),
                    cpoint.depth);

                match some_res {
                    Some((mut new_goals, new_env, new_range)) => {

                        new_goals.extend(goals_iter.cloned());
                        let cp0 = CPoint {
                            goals: new_goals,
                            env: new_env,
                            clause_range: 0..,
                            depth: cpoint.depth + 1
                        };

                        let mut cp1 = cpoint;
                        cp1.clause_range = new_range;

                        Soln::CPoints([cp0, cp1])
                    }
                    None => Soln::NoRule
                }
            }
            None => Soln::Res(cpoint.env)
        }
        
    }

    fn solve_goals<Env>(&self, goals: Self::Goals, env: Env, strategy: Strategy)
    -> CPointIter<'_, Self::Goals, Env, Self>
    {
        CPointIter {
            clause_db: self,
            cpoints: vec![
                CPoint::new(goals, env)
            ],
            strategy: strategy
        }
    }

    fn solve_goal<Goal, Env>(&self, goal: Goal, env: Env, strategy: Strategy)
    -> CPointIter<'_, Self::Goals, Env, Self>
    {
        //self.solve_goals(goal, env, strategy)
        unimplemented!()
    }
}

pub struct CPointIter<'a, Goals, Env, DB>
where
    DB: ?Sized
{
    clause_db: &'a DB,
    cpoints: Vec<CPoint<Goals, Env>>,
    strategy: Strategy
}

impl<'a, Goal, Env, DB> Iterator for CPointIter<'a, DB::Goals, Env, DB>
where
    DB::Head: Rename + Clone,
    Env: EnvTrait,
    Goal: Rewriting<Head=DB::Head, Env=Env>,
    DB::Goals: Rename + Extend<Goal> + Clone,
    DB: Index<RangeFrom<usize>, Output=[(DB::Goals, DB::Head)]>,

    Goal: Clone,
    for<'b> &'b DB::Goals: IntoIterator<Item=&'b Goal>,

    DB: DBTrait
{
    type Item = Env;

    fn next(&mut self) -> Option<Self::Item>
    where
    
    {
        loop {
            match self.cpoints.pop().map(|cp| self.clause_db.resolve(cp)) {
                Some(Soln::Res(env)) => return Some(env),
                Some(Soln::CPoints([cp0, cp1])) => match self.strategy {
                    
                    Strategy::DFS => self.cpoints.extend([cp1, cp0]),
                    Strategy::BFS => self.cpoints.extend([cp0, cp1]),
                    Strategy::DLS(n) => {
                        unimplemented!()
                    }
                }
                Some(Soln::NoRule) => continue,
                None => return None           
            }
        }
    }
}
