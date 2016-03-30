theory CAES2

imports Main

begin

(* all: true if every member of the list satisfies the predicate *)
fun all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"all f [] = True" |
"all f (h#t) = (f h \<and> all f t)"

(* exists: true is some member of the list satisfies the predicate. *)
fun exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"exists f [] = False" |
"exists f (h#t) = (if (f h) then True else exists f t)"

fun member :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
"member x [] = False" |
"member x (h#t) = (if x=h then True else member x t)"

(* stmt: statements *)
datatype stmt = Stmt "string"

datatype standard = PE | CCE | BRD

datatype issue = Issue "standard * stmt list"

fun issue_standard :: "issue \<Rightarrow> standard" where
"issue_standard (Issue (s,_)) = s"

fun issue_positions :: "issue \<Rightarrow> stmt list" where
"issue_positions (Issue (_,sl)) = sl"

datatype label = In | Out | Undecided
type_synonym labeling = "stmt \<Rightarrow> label option"

fun get :: "labeling \<Rightarrow> stmt \<Rightarrow> label" where
"get l s = (case l s of None \<Rightarrow> Undecided | Some x \<Rightarrow> x)"

(* weigher: the weight of an argument depends on the labels of its premises 
   and the labels of other positions of issues about the premises. Weights 
   are modeled here as integers in the range of 0 to 100. *)
type_synonym weigher = "labeling \<Rightarrow> stmt list \<Rightarrow> issue list => int"
type_synonym validator = "stmt list \<Rightarrow> stmt \<Rightarrow> bool"
datatype scheme = Scheme "weigher * validator"

fun scheme_weigher :: "scheme \<Rightarrow> weigher" where
"scheme_weigher (Scheme (w, _)) = w"

fun scheme_validator :: "scheme \<Rightarrow> validator" where
"scheme_validator(Scheme (_, v)) = v"

(* linked_argument: The weight of a cumulative argument is 100 if all its premises are In.
   Its weight is \<^bold>0 otherwise. *)
definition "linked_argument = 
   Scheme (\<lambda> l ps _ . if all (\<lambda> s . get l s = In) ps then 100 else 0,
           \<lambda> ps c . True)"

(* convergent_argument: The weight of a convergent argument is 100 if at least one of 
   its premises is In. Its weight is \<^bold>0 otherwise. *)
definition "convergent_argument =               
   Scheme (\<lambda> l ps _ . if exists (\<lambda> s . get l s = In) ps then 100 else 0,
           \<lambda> ps c . True)"

(* cumulative_argument: The weight of a cumulative argument equals the percentage of its
   premises which are In. *)
definition "cumulative_argument =
   Scheme (\<lambda> l ps _ . (int ((100::nat) * 
                       ((length (map (\<lambda> p . get l p = In) ps)) 
                        div (length ps)))),
           \<lambda> ps c . True)"

(* argument: scheme, premises, conclusion, not applicable statement *)
datatype arg = Arg "scheme * stmt list * stmt * stmt"

fun arg_scheme :: "arg \<Rightarrow> scheme" where
"arg_scheme (Arg(s,_,_,_)) = s"

fun arg_premises :: "arg \<Rightarrow> stmt list" where
"arg_premises (Arg(_,ps,_,_)) = ps"

fun arg_conclusion :: "arg \<Rightarrow> stmt" where
"arg_conclusion (Arg(_,_,c,_)) = c"

(* undercutter: the statement denoting the argument is not applicable *)
fun arg_undercutter :: "arg \<Rightarrow> stmt" where
"arg_undercutter (Arg(_,_,_,u)) = u"

(* argument graph: statements, assumptions, issues, arguments *)
datatype ag = Ag "stmt list * stmt list * issue list * arg list"

fun ag_stmts :: "ag \<Rightarrow> stmt list" where
"ag_stmts (Ag(sl,_,_,_)) = sl"

(* ag_asms: argument graph assumptions *)
fun ag_asms :: "ag \<Rightarrow> stmt list" where
"ag_asms (Ag(_,sl,_,_)) = sl"

fun ag_issues :: "ag \<Rightarrow> issue list" where
"ag_issues (Ag(_,_,il,_)) = il"

fun ag_args :: "ag \<Rightarrow> arg list" where
"ag_args (Ag(_,_,_,al)) = al"

fun undercut :: "labeling \<Rightarrow> arg \<Rightarrow> label" where
"undercut l a = get l (arg_undercutter(a))"

fun all_decided :: "(stmt list) \<Rightarrow> labeling \<Rightarrow> bool" where
"all_decided [] _ = True" |
"all_decided (h#t) l  = (((get l h) \<noteq> Undecided) \<and> (all_decided t l))"

fun applicable :: "labeling \<Rightarrow> arg \<Rightarrow> bool" where
"applicable l a = (((undercut l a) = Out) \<and> (all_decided (arg_premises a) l))"

(* pro_args: arguments with the given conclusion *)
fun pro_args :: "ag \<Rightarrow> stmt \<Rightarrow> arg list" where
"pro_args g s = [ arg \<leftarrow> (ag_args g) . arg_conclusion arg = s ]" 

(* stmt_issue: the issue of a statement, if it is at issue. Assumes 
   that every statement is a position of at most one issue. *) 
fun stmt_issue :: "ag \<Rightarrow> stmt \<Rightarrow> issue option" where
"stmt_issue g s = List.find (\<lambda> i . member s (issue_positions i)) (ag_issues g)" 

(* contraries: the other positions of an issue *)
fun contraries :: "issue  \<Rightarrow> stmt \<Rightarrow> stmt list" where
"contraries i p = remove1 p (issue_positions i)"

fun in_position :: "labeling \<Rightarrow> issue \<Rightarrow> stmt option" where
"in_position l i = List.find (\<lambda> p . get l p = In) (issue_positions i)"

(* rejectable_positions: positions which are contrary to some In position *)
fun rejectable_positions :: "labeling \<Rightarrow> ag \<Rightarrow> stmt list" where
"rejectable_positions l g = concat (map (\<lambda> i . case (in_position l i) of 
                                          None \<Rightarrow> [] 
                                        | Some p \<Rightarrow> contraries i p) 
                                   (ag_issues g))"

(* con_args: arguments pro other positions of the issue of the statement *)
fun con_args :: "ag \<Rightarrow> stmt \<Rightarrow> arg list" where
"con_args g s = (case stmt_issue g s of
                      None \<Rightarrow> [] 
                    | Some i \<Rightarrow> concat (map (\<lambda> p . pro_args g p) 
                                            (contraries i s)))" 

(* issue_args: the arguments for all positions of an issue *)
fun issue_args :: "ag \<Rightarrow> issue \<Rightarrow> arg list" where
"issue_args g i = concat (map (\<lambda> p . pro_args g p) (issue_positions i))"

(* resolvable: an issue is resolvable if all arguments for all positions are 
   either undercut or applicable *)
fun resolvable :: "labeling \<Rightarrow> ag \<Rightarrow> issue \<Rightarrow> bool" where
"resolvable l g i = (all (\<lambda> arg . (undercut l arg = In) \<or> (applicable l arg))
                         (issue_args g i))"  

fun set_labels :: "labeling \<Rightarrow> (stmt * label) list \<Rightarrow> labeling" where
"set_labels old new = old ++ (map_of new)"

fun arg_weight :: "labeling \<Rightarrow> ag \<Rightarrow> arg \<Rightarrow> int" where
"arg_weight l g a = ((scheme_weigher (arg_scheme a))
                        l (arg_premises a) (ag_issues g))"

(* A statement is supported in a labeling if it is the conclusion of at least one 
   argument with a weight greater than 0 in the labeling *)
fun supported :: "labeling \<Rightarrow> ag \<Rightarrow> stmt \<Rightarrow> bool" where
"supported l g s = exists (\<lambda> a . (arg_weight l g a) > 0) 
                          (pro_args g s)"

fun unsupported :: "labeling \<Rightarrow> ag \<Rightarrow> stmt \<Rightarrow> bool" where
"unsupported l g s = all (\<lambda> a . undercut l a = In 
                              \<or> ((all (\<lambda> p . get l p \<noteq> Undecided) 
                                     (arg_premises a)) \<and>
                                  (arg_weight l g a) > 0))
                         (pro_args g s)"

(* stronger: an argument is stronger than another if it has more weight *)
fun stronger :: "labeling \<Rightarrow> issue list \<Rightarrow> arg \<Rightarrow> arg \<Rightarrow> bool" where
"stronger l is a\<^sub>1 a\<^sub>2 = 
  (((scheme_weigher (arg_scheme a\<^sub>2)) l (arg_premises a\<^sub>2) is) >
   ((scheme_weigher (arg_scheme a\<^sub>1)) l (arg_premises a\<^sub>1) is))"

fun decide :: "issue \<Rightarrow> stmt \<Rightarrow> (stmt * label) list" where
"decide i p  = (p,In) # (map (\<lambda> q . (q, Out)) (contraries i p))" 

definition "\<alpha> = 50"
definition "\<beta> = 30"

fun weight_of_strongest_arg :: "labeling \<Rightarrow> ag \<Rightarrow> arg list \<Rightarrow> int" where
"weight_of_strongest_arg l g as = 
  (fold (\<lambda> a w . max w (arg_weight l g a))
        as
        0)"

fun satisfies :: "standard \<Rightarrow> labeling \<Rightarrow> ag \<Rightarrow> stmt \<Rightarrow> bool" where
"satisfies PE l g s = exists (\<lambda> a\<^sub>1 . all (\<lambda> a\<^sub>2 . stronger l (ag_issues g) a\<^sub>1 a\<^sub>2)
                                         (con_args g s))  
                             (pro_args g s)" |
"satisfies CCE l g s = (exists (\<lambda> a\<^sub>1 . all (\<lambda> a\<^sub>2 . stronger l (ag_issues g) a\<^sub>1 a\<^sub>2)
                                         (con_args g s))  
                               (pro_args g s) \<and>  
                       ((weight_of_strongest_arg l g (pro_args g s)) - 
                        (weight_of_strongest_arg l g (con_args g s)) > \<alpha>))" |
"satisfies BRD l g s = (let wp = weight_of_strongest_arg l g (pro_args g s);
                            wc = weight_of_strongest_arg l g (con_args g s)
                        in (exists (\<lambda> a\<^sub>1 . all (\<lambda> a\<^sub>2 . stronger l (ag_issues g) a\<^sub>1 a\<^sub>2)
                                          (con_args g s))  
                                   (pro_args g s)  \<and>
                            (wp - wc > \<alpha>) \<and>
                            (wc < \<beta>)))"                                             

(* resolve an issue, returning the preferred/winning position, or None, if the 
   issue is not resolvable *)
fun resolve :: "labeling \<Rightarrow> ag \<Rightarrow> issue \<Rightarrow> stmt option" where
"resolve l g i = (if \<not>(resolvable l g i) 
                   then None
                   else (List.find (\<lambda> p . satisfies (issue_standard i) l g p)
                                                 (issue_positions i)))"

(* consistent: an argument graph is consistent if no more than one position of each
   issue is assumed to be true. *)
fun consistent :: "ag \<Rightarrow> bool" where
"consistent g = all (\<lambda> i . (length (filter (\<lambda> p. member p (ag_asms g))
                                           (issue_positions i))) \<le> 1)
                    (ag_issues g)"

fun inconsistent :: "ag \<Rightarrow> bool" where
"inconsistent g = (\<not>(consistent g))"

fun update_label :: "labeling \<Rightarrow> ag \<Rightarrow> stmt \<Rightarrow> (stmt * label)" where
"update_label l g s = 
  (if get l s \<noteq> Undecided then
    (s, get l s)
   else 
    (if member s (ag_asms g) then (s,In)
     else (case stmt_issue g s of
                   None \<Rightarrow> (if supported l g s then (s,In) 
                            else (if unsupported l g s then (s,Out) else (s,Undecided)))
                 | Some i \<Rightarrow> (case resolve l g i of 
                                None \<Rightarrow> (s,Undecided) 
                              | Some p \<Rightarrow> (if p = s then (s,In) else (s,Out))))))" 

(* F: the characteristic function of the labeling lattice. *)
fun F :: "ag \<Rightarrow> labeling \<Rightarrow> labeling" where
"F g l =  set_labels l (map (\<lambda> s . update_label l g s) (ag_stmts g))"

(* label_stmts: update the label every statement of an argument graph. 
   The boolean value indicates whether the labeling of any statement has changed. *)
fun label_stmts :: "stmt list \<Rightarrow> (labeling * bool) \<Rightarrow> ag \<Rightarrow> (labeling * bool)" where
  "label_stmts [] p _ = p" 
| "label_stmts (h#t) (l\<^sub>1,changed) g = 
    (let old_label = get l\<^sub>1 h;
         (_, new_label) = update_label l\<^sub>1 g h in
     if new_label = old_label then
        label_stmts t (l\<^sub>1,changed) g
     else label_stmts t (set_labels l\<^sub>1 [(h, new_label)], True) g)"              

(* label_ag: Recursively label the statements of the argument graph
   until the labeling is not changed. *)
fun label_ag :: "labeling \<Rightarrow> ag \<Rightarrow> labeling" where
"label_ag l\<^sub>1 g = (let (l\<^sub>2, changed) = label_stmts (ag_stmts g) (l\<^sub>1,False) g in
                  if \<not>changed then l\<^sub>1 else label_ag l\<^sub>2 g)"

fun grounded_labeling :: "ag \<Rightarrow> labeling" where
"grounded_labeling g = label_ag Map.empty g"

end

