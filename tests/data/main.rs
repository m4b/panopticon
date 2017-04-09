#[macro_use]
extern crate log;
extern crate env_logger;

extern crate panopticon;
extern crate rustc_serialize;
extern crate graph_algos;
extern crate uuid;
extern crate rayon;
extern crate serde_json;
extern crate serde;
#[macro_use]
extern crate serde_derive;

use panopticon::{
    Project,
    Function,
    CallTarget,
    ControlFlowTarget,
    Rvalue,
    Result,
    ssa_convertion,
    Lvalue,
    Architecture,
    approximate,
    Kset,
};
use panopticon::amd64;
use panopticon::loader;

use std::collections::{
    HashMap,
    HashSet,
};
use std::fmt::Debug;

use graph_algos::{
    VertexListGraphTrait,
    MutableGraphTrait,
    GraphTrait,
    IncidenceGraphTrait,
};

use std::env;
use std::path::Path;
use uuid::Uuid;

//use graph_algos::traits::{VertexGraph, Graph};


#[derive(Serialize, Deserialize, Debug)]
pub struct Metainfo {
    pub kind: String,
    pub name: Option<String>,
    pub uuid: String,
    pub entry_point: Option<u64>,
    pub calls: Vec<String>,
}

/// JSON describing the function".to_string() with UUID `arg`.
///
/// The JSON looks like this:
/// ```json
/// {
///     "kind": "function".to_string()",     // or "symbol" or "todo"
///     "name": "func_001",     // not present if type is "todo"
///     "uuid": <UUID>,
///     "entry_point": 0x1002,  // optional: entry point
///     "calls": [              // outgoing calls
///         <UUID>,
///         <UUID>,
///         ...
///     ]
/// }
/// ```
impl Metainfo {
    pub fn new(uuid: &Uuid, project: &Project) -> Result<Metainfo> {
        if let Some((vx,prog)) = project.find_call_target_by_uuid(&uuid) {
            // collect called functions' UUIDs
            let calls = prog.call_graph.out_edges(vx).
                map(|x| prog.call_graph.target(x)).
                filter_map(|x| prog.call_graph.vertex_label(x)).
                map(|x| x.uuid().to_string()).
                collect();

            // match function
            match prog.call_graph.vertex_label(vx) {
                Some(&CallTarget::Concrete(Function{ ref uuid, ref name, entry_point: Some(ref ent), cflow_graph: ref cg,..})) =>
                // match entry point
                    match cg.vertex_label(*ent) {
                        Some(&ControlFlowTarget::Resolved(ref bb)) =>
                            return Ok(Metainfo{ kind: "function".to_string(), name: Some(name.clone()), uuid: uuid.to_string(), entry_point: Some(bb.area.start), calls: calls }),
                        Some(&ControlFlowTarget::Unresolved(Rvalue::Constant{ value: c,.. })) =>
                            return Ok(Metainfo{ kind: "function".to_string(), name: Some(name.clone()), uuid: uuid.to_string(), entry_point: Some(c), calls: calls }),
                        Some(&ControlFlowTarget::Unresolved(_)) =>
                            return Ok(Metainfo{ kind: "function".to_string(), name: Some(name.clone()), uuid: uuid.to_string(), entry_point: None, calls: calls }),
                        Some(&ControlFlowTarget::Failed(pos,_)) =>
                            return Ok(Metainfo{ kind: "function".to_string(), name: Some(name.clone()), uuid: uuid.to_string(), entry_point: Some(pos), calls: calls }),
                        None => unreachable!(),
                    },
                Some(&CallTarget::Concrete(Function{ ref uuid, ref name, entry_point: None,..})) =>
                    return Ok(Metainfo{ kind: "function".to_string(), name: Some(name.clone()), uuid: uuid.to_string(), entry_point: None, calls: calls }),
                Some(&CallTarget::Symbolic(ref sym,ref uuid)) =>
                    return Ok(Metainfo{ kind: "symbol".to_string(), name: Some(sym.clone()), uuid: uuid.to_string(), entry_point: None, calls: calls }),
                Some(&CallTarget::Todo(Rvalue::Constant{ value: a,.. },_,ref uuid)) =>
                    return Ok(Metainfo{ kind: "todo".to_string(), name: None, uuid: uuid.to_string(), entry_point: Some(a), calls: calls }),
                Some(&CallTarget::Todo(_,_,ref uuid)) =>
                    return Ok(Metainfo{ kind: "todo".to_string(), name: None, uuid: uuid.to_string(), entry_point: None, calls: calls }),
                None =>
                    return Err("Internal error".into()),
            }
        } else {
            return Err("No function found for this UUID".into())
        }
    }
}

#[derive(Serialize, Deserialize, Debug)]
struct CfgEdge {
    from: String,
    to: String,
}

#[derive(Serialize, Deserialize, Debug)]
struct CfgMnemonic {
    opcode: String,
    region: String,
    offset: u64,
    comment: String,
    args: Vec<CfgOperand>,
}

#[derive(Serialize, Deserialize, Debug)]
struct CfgOperand {
    kind: String, // constant, variable, function, literal
    display: String, // string to display
    data: String, // constant: value, variable: ssa var, function: UUID, literal: empty string
}

#[derive(Serialize, Deserialize, Debug)]
struct ControlFlowGraph {
    entry_point: Option<String>,
    nodes: Vec<String>,
    edges: Vec<CfgEdge>,
    code: HashMap<String,Vec<CfgMnemonic>>,
    targets: HashMap<String,String>,
    errors: HashMap<String,String>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Analysis {
    program: Vec<ControlFlowGraph>,
}

impl Analysis {
    pub fn new (_project: &Project) -> Result<Analysis> {
        Err("into".into())
    }
}

#[derive(Debug, Clone)]
struct Todo {
    name: String,
    uuid: Uuid,
    entry: u64,
    size: usize,
}


fn disassemble<A: 'static + Architecture + Debug>(todos: &[Todo], project: &mut Project, cfg: &A::Configuration) -> Vec<Uuid>
where A::Configuration: Debug + Sync, A::Token: Sync + Send {
    let root = project.data.dependencies.vertex_label(project.data.root).unwrap();
    let mut program = &mut project.code[0];
    use rayon::prelude::*;
    let funcs = todos.par_iter().map(|ref todo| -> Result<Function> {
        let entry = todo.entry;
        //println!("start new function".to_string() {:?} at {:?}",&todo.uuid,entry);
        let mut func = {
            let name = todo.name.clone();
            Function::with_uuid(name, todo.uuid, root.name().clone())
        };
        func = {
            let mut func = {
                Function::disassemble::<A>(Some(func),cfg.clone(),&root,entry)
            };
            func.entry_point = func.find_basic_block_by_start(entry);
            func
        };

        if func.cflow_graph.num_vertices() == 0 || func.entry_point.is_none() {
            //println!("failed to disassemble for {}", func.name);

            //let uu = func.uuid.clone();
            // let mut program: &mut Program = project.find_program_by_uuid_mut(&program.uuid).unwrap();
            // program.insert(CallTarget::Concrete(func));

            //try!(Controller::emit(FINISHED_FUNCTION,&uu.to_string()));
            return Err("bad".into());
            //(vec![]);
        }
        //println!("primary pass done");
        //println!("{:#}", json::encode(&func).unwrap());
        let mut fixpoint = func.entry_point.is_none();

        while !fixpoint {
            fixpoint = true;
            ssa_convertion(&mut func);

            let vals = try!(approximate::<Kset>(&func));
            let vxs = { func.cflow_graph.vertices().collect::<Vec<_>>() };
            let mut resolved_jumps = HashSet::<u64>::new();

            for &vx in vxs.iter() {
                if let Some(&mut ControlFlowTarget::Unresolved(ref mut var@Rvalue::Variable{..})) = func.cflow_graph.vertex_label_mut(vx) {
                    if let Some(&Kset::Set(ref v)) = vals.get(&Lvalue::from_rvalue(var.clone()).unwrap()) {
                        if let Some(&(val,sz)) = v.first() {
                            *var = Rvalue::Constant{ value: val, size: sz };
                            fixpoint = true;
                            //println!("resolved {:?} to {:?}",var,val);
                            resolved_jumps.insert(val);
                        }
                    }
                }
            }

            for addr in resolved_jumps {
                //println!("continue at {:?}",addr);
                func = {
                    let mut func = {
                        Function::disassemble::<A>(Some(func),cfg.clone(),&root,addr)
                    };

                    func.entry_point = func.find_basic_block_by_start(entry);

                    func
                };
            }
            debug!("todo: {:?} entry: {:#x}", &todo, todo.entry);
        }
        Ok(func)
    }).collect::<Vec<Result<Function>>>();
    
    println!("correctly disassembled {}/{} functions",  
             funcs.par_iter()
             .map(|ref i| if i.is_ok() { 1 } else { 0 })
             .sum::<u32>(),
             todos.len()
    );
    let mut nfs = Vec::new();
    for f in funcs {
        match f {
            Ok(f) => {
                //let name = f.name.clone();
                let newfuncs = program.insert(CallTarget::Concrete(f));
                // for uuid in &newfuncs {
                //     let f = program.find_function_by_uuid_mut(uuid);

                // }
                //println!("new funcs: {:?}", newfuncs);
                nfs.extend_from_slice(&newfuncs);
            },
            _ => {}
        }
    }
    nfs
}

fn analyze<A: 'static + Architecture + Debug>(mut project: Project, sym: &str, cfg: A::Configuration) -> panopticon::result::Result<()>
where A::Configuration: Debug + Sync, A::Token: Sync + Send {
    let get_todos = |project : &Project| -> Vec<Todo> {
        let program = &project.code[0];
        program.call_graph.vertices().filter_map(|x| {
            match program.call_graph.vertex_label(x) {
                Some (&CallTarget::Todo(Rvalue::Constant{value, size}, ref name, uuid)) => {
                    let name = name.clone().unwrap_or(format!("func_{:x}", value));
                    Some(
                        Todo {
                            name: name,
                            uuid: uuid,
                            entry: value,
                            size: size,
                        })
                },
                _ => None
            }
        }).collect::<Vec<_>>()
    };

    let mut todos = get_todos(&project);
    while !todos.is_empty() {
        let newuuids = disassemble::<A>(todos.as_slice(), &mut project, &cfg);
        debug!("newfns: {:?}", &newuuids);
        println!("new todos: {}", newuuids.len());
        todos = get_todos(&project);
        if newuuids.len() == 0 { break }
    }
    let program = &project.code[0];
    if let Some(ct) = program.find_call_target_by_name(sym) {
        println!("{}", ct.display_with(program));
    }

    for vx in program.call_graph.vertices() {
        if let Some(lb) = program.call_graph.vertex_label(vx) {
            let uuid = lb.uuid();
            let metainfo = Metainfo::new(&uuid, &project)?;
            let serialized = serde_json::to_string(&metainfo).unwrap();
            println!("{:#}", serialized);
        }
    }

    //println!("program: {:#?}", &program);
    Ok(())
}

fn run(path: &str, sym: &str) -> panopticon::result::Result<()> {
    let (project, machine) = panopticon::loader::load(Path::new(&path))?;
    match machine {
        loader::Machine::Amd64 => analyze::<amd64::Amd64>(project, sym, amd64::Mode::Long),
        loader::Machine::Ia32 => analyze::<amd64::Amd64>(project, sym, amd64::Mode::Protected),
        _ => Ok(())
    }
}

fn main () {
    env_logger::init().unwrap();
    let mut bin = String::new();
    for (i, arg) in env::args().enumerate() {
        if i == 1 {
            bin = arg.clone();
        }
        if i == 2 {
            match run(&bin, &arg) {
                Err(err) => println!("{:?}", err),
                Ok(()) => ()
            }

        }
    }
}
