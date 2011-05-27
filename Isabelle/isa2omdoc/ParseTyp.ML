signature ParseTyp =
sig
    val TypToOMOBJ : (typ * CDLookup.environment) -> (string * string list)
end;

structure ParseTyp : ParseTyp = 
struct
open utility
fun TypToOMOBJ (T, env)=
    let 
	fun escape([])=[]| 
	    escape(name)= if hd(name)="&" then "&amp;"::escape(tl(name)) else
			  if hd(name)="<" then "&lt;"::escape(tl(name)) else
			  if hd(name)=">" then "&gt;"::escape(tl(name)) else
			  if hd(name)="\"" then "&quot;"::escape(tl(name)) else
			  if hd(name)="'" then "&apos;"::escape(tl(name)) else hd(name)::escape(tl(name));
	fun escaped(name)=implode(escape(explode(name)));
	fun print_sort ([], env) = ""|
	    print_sort (c::C, env) = 
		let
			val x= CDLookup.lookup (2, env) c
		in
			"<om:OMS cd=\""^ escaped(#1 x) ^"\" name=\""^ escaped(getName(c)) ^ "\"/>\n" ^ print_sort(C, env)
		end
	fun getVar(Type(Name,nil))=[]|
            getVar(Type(Name,X::nil))= getVar(X)|
	    getVar(Type(Name,TypList))= foldl op@ [] (map getVar TypList) |
	    getVar(TFree(Name,Sort))=[]|
	    getVar(TVar((Name,Index),Sort))=[escaped(Name)^Int.toString(Index)];
	fun toOmdoc(Type(Name,nil), env)=
		let 
			val x = CDLookup.lookup (1, env) Name
		in
		
		 "<om:OMS cd=\""^ escaped(#1 x) ^"\" name=\"" ^ escaped(getName(Name)) ^ "\"/>\n"
		
		end|
	    toOmdoc(Type(Name, TypList), env)=
		let 
			val x = CDLookup.lookup (1, env) Name
			fun go_list([], env)=""|
			    go_list(TList,env)=toOmdoc(hd(TList),env) ^ go_list(tl(TList),env);
			in
				 "<om:OMA>\n" 
				 ^ "<om:OMS cd=\""^ escaped(#1 x) ^"\" name=\"" ^ escaped(getName(Name)) ^ "\"/>\n"
				 ^ go_list(TypList, env) 
				 ^ "</om:OMA>\n"
			end|
	    toOmdoc(TFree(Name,Sort), env) =
			"<om:OMA>\n"
			^ "<om:OMS cd=\"Pure\" name=\"" ^ escaped(getName(Name)) ^ "\"/>\n"
			^ "<om:OMA>\n"
			^ "<om:OMS cd=\"Pure\" name=\"free_sort\"/>\n"
			^ print_sort(Sort, env)
			^ "</om:OMA>\n"
			^ "</om:OMA>\n"
			|
	    toOmdoc(TVar((Name, Index),Sort), env)=
			"<om:OMV name=\""^escaped(Name)^Int.toString(Index)^"\"/>\n"
	    val vars = utility.uniquify (utility.mergesort op< (getVar(T))); 
   in	
	(toOmdoc(T, env),vars)
    end
end;
