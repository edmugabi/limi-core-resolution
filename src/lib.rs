#![allow(warnings, unused)]

extern crate log;
use ::std::fmt;
use log::debug;
use std::ops::{Index, RangeFrom};

pub trait PrettyPrint {
    fn pretty_print(&self) -> String;
}

pub trait Unify<Head, Env> {
    type Err;
    fn unify(&self, other: &Head, env: &mut Env) -> Result<(), Self::Err>;
}

pub trait Subst<Env> {
    type Res;
    fn subst(&self, env: &Env) -> Self::Res;
}

pub trait EnvTrait: std::fmt::Debug {
    fn empty() -> Self;
    fn compose(self, other: &Self) -> Self;
}

pub trait Rename {
    fn rename(&mut self, index: usize);
}

impl<T, Ts> Rename for Ts
where
    for<'a> &'a mut Ts: IntoIterator<Item = &'a mut T>,
    T: Rename,
{
    fn rename(&mut self, index: usize) {
        self.into_iter().for_each(|t: &mut T| t.rename(index))
    }
}

pub enum Strategy {
    DFS,
    BFS,
    DLS(usize),
}

pub struct CPoint<DB, Goals, Env>
{
    goals: Goals,
    env: Env,
    db: DB,
    depth: usize,
}

impl<'a, DB, Goals, Env> CPoint<DB, Goals, Env> {
    fn new(goals: Goals, env: Env, db: DB) -> Self {
        Self {
            goals,
            env,
            db,
            depth: 1,
        }
    }
}

pub enum Soln<DB, Goals, Env>
{
    CPoints([CPoint<DB, Goals, Env>; 2]),
    CPoint(CPoint<DB, Goals, Env>),
    Res(Env),
    NoRule,
}

impl<'a, T, Goals, Head> DBTrait for T
where
    Goals: 'a,
    Head: 'a,
    T: Iterator<Item=&'a (Goals, Head)>
{
    type Goals = Goals;
    type Head = Head;
}

pub trait DBTrait
where
{
    type Goals;
    type Head;

    fn resolve_one_step<'b, Goal, Env>(
        mut self,
        goal: &Goal,
        env: &Env,
        // uses the depth as renaming index
        renaming_index: usize,
    ) -> Option<(Self::Goals, Env, Self)>
    where
        // resolve one step
        Self::Head: Rename + Clone + fmt::Debug,
        Env: EnvTrait,
        Goal: Subst<Env>,
        Goal::Res: Unify<Self::Head, Env> + fmt::Debug,
        Self::Goals: Rename +  Clone,
        Self: Sized,
        Self::Goals: 'b,
        Self::Head: 'b,
        Self: Iterator<Item = &'b (Self::Goals, Self::Head)>,
    {
        self.find_map(|(body, head)| {
            let mut head = head.clone();
            head.rename(renaming_index);

            let goal = goal.subst(env);

            let mut new_env = Env::empty();
            match goal.unify(&head, &mut new_env) {
                Ok(()) => {
                    debug!(
                        "\nHead:     {:?}\ngoal:     {:?}\nEnv:      {:?}\n",
                        head, goal, new_env
                    );
                    // debug!("", goal);
                    // debug!("Env:      {:?}\n", new_env);
                    let ret_env = new_env.compose(env);

                    //debug!("db_index: {}, depth: {}", clause_range.start+i, renaming_index);
                    
      
   
                    // an optimisation where the body is renamed only when necessary
                    let mut new_body: Self::Goals = body.clone();
                    new_body.rename(renaming_index);

                    return Some((new_body, ret_env));
                }
                Err(_) => None,
            }
        })
        .map(|(body, env)| (body, env, self))
    }

    fn resolve<'b,  Goal, Env, F>(
        self,
        cpoint: CPoint<Self, Self::Goals, Env>,
        solve_primitive: F,
    ) -> Soln<Self, Self::Goals, Env>
    where
        // resolve_one_step
        Self::Head: Rename + Clone + fmt::Debug,
        Env: EnvTrait,
        Goal: Subst<Env>,
        Goal::Res: Unify<Self::Head, Env> + fmt::Debug,
        Self::Goals: Rename +  Clone,
        Self: Sized,
        Self::Goals: 'b,
        Self::Head: 'b,
        Self: Iterator<Item = &'b (Self::Goals, Self::Head)>,
        // resolve
        Goal: Clone,
        Self: Clone,
        Self::Goals: Extend<Goal>,
        for<'c> &'c Self::Goals: IntoIterator<Item=&'c Goal>,
        Self::Goals: FromIterator<Goal>,
        F: Fn(&Goal, &Env) -> Option<Env>
    {
        let mut goals_iter = (&cpoint.goals).into_iter();

        match goals_iter.next() {
            Some(goal_ref) => {

                match solve_primitive(goal_ref, &cpoint.env) {
                    Some(new_env) => {
                        let new_goals = goals_iter.cloned().collect();

                        let ret_env = new_env.compose(&cpoint.env);
                        let mut cp = cpoint;
                        cp.env = ret_env;
                        cp.goals = new_goals;
                        return Soln::CPoint(cp)
                    },
                    None => {
                
                        let some_res = cpoint.db.clone().resolve_one_step(
                            goal_ref,
                            &cpoint.env,
                            cpoint.depth);

                        match some_res {
                            Some((mut new_goals, new_env, rest_db)) => {
                                new_goals.extend(goals_iter.cloned());
                                let cp0 = CPoint {
                                    goals: new_goals,
                                    env: new_env,
                                    db: self,
                                    depth: cpoint.depth + 1,
                                };

                                let mut cp1 = cpoint;
                                cp1.db = rest_db;

                                Soln::CPoints([cp0, cp1])
                            }
                            None => Soln::NoRule,
                        }
                    }
                }


            }
            None => Soln::Res(cpoint.env),
        }
    }

    
    fn solve_goals_with<'b, Env, F>(
        self,
        goals: Self::Goals,
        env: Env,
        solve_primitive: F,
        strategy: Strategy,
    ) -> CPointIter<Self, Self::Goals, Env, F>
    where
        Self: Sized + Clone
    {
        CPointIter {
            clause_db: self.clone(),
            cpoints: vec![CPoint::new(goals, env, self)],
            solve_primitive: solve_primitive,
            strategy: strategy,
        }
    }

    fn solve_goals<'b, Goal, Env: EnvTrait, F>(
        self,
        goals: Self::Goals,
        solve_primitive: F
    ) -> CPointIter<Self, Self::Goals, Env, F>
    where
        Self: Sized + Clone
    {
        //TODO change to IDFS or SLG
        self.solve_goals_with(goals, Env::empty(), solve_primitive, Strategy::DFS)
    }
}

pub struct CPointIter<DB, Goals, Env, F>
{
    clause_db: DB,
    cpoints: Vec<CPoint<DB, Goals, Env>>,
    solve_primitive: F,
    strategy: Strategy,
}

impl<'a, 'b, DB,Goal, Env, F> Iterator for CPointIter<DB, DB::Goals, Env, F>
where
    // resolve_one_step
    DB::Head: Rename + Clone + fmt::Debug,
    Env: EnvTrait,
    Goal: Subst<Env>,
    Goal::Res: Unify<DB::Head, Env> + fmt::Debug,
    DB::Goals: Rename +  Clone,
    DB: Sized,
    DB::Goals: 'b,
    DB::Head: 'b,
    DB: Iterator<Item = &'b (DB::Goals, DB::Head)>,

    // resolve
    Goal: Clone,
    DB: Clone,
    DB::Goals: Extend<Goal>,
    for<'c> &'c DB::Goals: IntoIterator<Item=&'c Goal>,
    F: Fn(&Goal, &Env) -> Option<Env>,
    DB::Goals: FromIterator<Goal>,
    // iterator
    DB: DBTrait,
{
    type Item = Env;

    fn next(&mut self) -> Option<Self::Item>
    {
        loop {

            let db = self.clause_db.clone();
            let some_soln = self.cpoints.pop()
            .map(|cp| {
                 //debug!("\n\n\n-----------------------------");
                //debug!("trying cp, clause_index = {:?}", cp.db);
                db.resolve(cp, &self.solve_primitive)
            });
            match some_soln {
                Some(Soln::Res(env)) => return Some(env),
                Some(Soln::CPoints([cp0, cp1])) => match self.strategy {
                    Strategy::DFS => self.cpoints.extend([cp1, cp0]),
                    Strategy::BFS => self.cpoints.extend([cp0, cp1]),
                    Strategy::DLS(n) => {
                        unimplemented!()
                    }
                },
                Some(Soln::CPoint(cp)) => self.cpoints.push(cp),
                Some(Soln::NoRule) => continue,
                None => return None,
            }
        }
    }
}


trait Resolve
where

{}