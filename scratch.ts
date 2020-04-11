
interface pos_info {
    line : number, column : number
}
interface pos_range {
    begin : pos_info, end : pos_info
}
interface location {
    fileName : string,
    range : pos_range;
}

interface info_data {

}

interface info_manager {
    fileName : string,
    data : pos_info ⇀ info_data[]
}

type DetailLevel = "Default" | "Elaboration" | "CrossModule" | "Max" // whatever
type LogState = "Created" | "Running" | "Cancelled"  | "Finished"

interface log_entry {

}

interface node {
    entries : log_entry;
    location : location,
    description : string;
    state : LogState;
    children : name ⇀ node
}

interface log_tree {
    root : node,
    mutex,
    listeners;
}

interface info_data {

}

type module_id = string;

interface cancellable {
    cancel();
}

interface cancelation_token {
    mutex,
    cancelled : boolean,
    children : cancellable[];
    expired_children : number;
}

/** For storing parser checkpoints in a file/buffer. I */
interface snapshot {
    environment,
    name_generator,
    local_level_decls,
    local_expr_decls,
    options,
    parser_scope_stack
    pos : pos_info
    etc;
}

/** The result of partially parsing a module. Aka 'snapshots;.
 *  Note how `next` contains the next snapshot available. */
interface module_parser_result {
    /** The span of source that this result is responsible for parsing?  */
    range : pos_range;
    snapshot_at_end : snapshot;
    cancel : cancelation_token;
    lt : node;
    next : task<module_parser_result>;
}

/** A virtual interface for loading lean modules by name.
 * In the case of running lean in batch mode this is from disk.
 * In the case of running as a language server this is other files open in the editor.
 */
interface module_vfs {}

/** A module is just a file or olean. */
interface module_info {
    dependencies;
    out_of_date : boolean;
    hashes,
    contents : string,
    id : module_id;
    result : task<parse_result>
    /** This is a daisychain of module_parser_results starting at the beginning, navigate with ->next.  */
    snapshots? : module_parser_result;
    cancel : cancellation_token;
    /** A log tree node. */
    lt : node;
}

interface module_manager  {
    path : search_path;
    env : environment;
    ios : io_state;
    vfs : module_vfs;
    lt : node;
    mutex;
    modules : module_id ⇀ module_info
}

interface module_parser {
    parser : parser,
    end_pos : pos_info,
    separate_tasks : boolean;
    save_info : boolean;
    in : string_stream;
}

type token_context = "none"|" expr"|" notation"|" option"|" import"|" interactive_tactic"|" attribute"|" namespc"|" field"|" single_completion"

interface server {
    path : search_path,
    opts : options,
    io_state,
    open_files : string ⇀ editor_file
    lt : log_tree,
    environment
}

interface break_at_pos_exception {
    token_info : {
        pos : pos_info,
        token : name,
        context : token_context,
        param : name,
        tac_param_idx ?: number
    }
    /** THis is the position of the tactic whose information should be displayed? Not clear.  */
    goal_pos?: pos_info
}

/*

How it works

1. client makes an `info` request. We have the 'module_info' and the position. We have a json object `record` that we need to fill up with information to send back to the server.
2. run `parse_breaking_at_pos(module_info, pos)`. This does the following:
3. get the closest snapshot to the position in the module. This is a module_parser_result.
4. set up this snapshot; give it a new log tree, a new cancellation token and set `next` to be null.
5. Make a new module_parser which is instructed to break at the given position.
6. `resume` this parser, which amounts to setting the parsers' members with the snapshot and then running it.
7. the parser will throw a `break_at_pos_exception` when it reaches the pos. Then we can read off the parser state for this precise position.
8. now we run `report_info` with all of this stuff, including the options and environment and io_state. In this method the following occrus:
9. look at the token that we broke on; each token has a 'context', found above. Which is used to determine the 'info' that should be produced for the token.
   eg if it's an import we add some information about where the imported file is or if its a constant we add the docstring etc etc.
10. After this step, we iterate through all of the `info_manager`s _on the `server`_. [todo] I can't quite beleive this works. What is updating the log tree?
11. We go through _all_ of the info_managers and then eventually find one for the given position.
12. Then this info_manager reports for that position.

Some questions:
- why is infomanager needed? I think it is needed because it holds the cache of the state.
- why can you get away with using the server's log tree? I guess it holds the log tree for the entire state.

From Gabriel:

Ok, let me give you a high-level overview. There are essentially a few different kinds of information that can be passed back to the editor:
1. Error messages (this is everything that has a wavy line in vscode, i.e. a "diagnostics")
2. Name of the constant under the cursor, type of the constant, file & position of the declaration, etc. (-> shown on hover)
3. Tactic states
4. Holes
No. 1 is always transferred to the editor eagerly. No. 2-4 are only sent when you query them, these are the ones that are stored in the info_manager, and they do not appear as diagnostics.
  7:13 PM

I think save_info_thunk can only show information that is essentially a tactic state.
  7:14 PM

IIRC all tactic states are added in Lean code (grep for save_info_thunk).
  7:16 PM

For _ we actually don't show a tactic state. It's just a plain error message (that happens to contain a tactic state..).
  7:19 PM

Your general approach of adding a new info_data_cell looks ok, depending on what you want to add.
  7:20 PM

The scoped_info_manager is part of the wonderful Lean 3 approach of using global variables (ok, thread-local) to pass around objects.... It just sets the global info manager variable to the argument while the scoped_info_manager is in scope, afterwards it is reset.
  7:24 PM

If you want to add stuff to the info manager from Lean code, then copy&paste tactic_save_info_thunk. If you're in the elaborator in c++, look at elaborator::save_identifier_info.
  7:24 PM

Also check out save_type_info, this is another way to add stuff to the info manager from Lean.

*/