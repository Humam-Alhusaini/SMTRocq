"""Syntax-directed Gallina expression emission shared by the signature compilers."""
import re

def parse_ir(s):
 tokens=re.findall(r'"(?:[^"]|"")*"|[()\[\];]|[A-Za-z_][A-Za-z_0-9]*|[0-9]+',s);i=0
 def visit():
  nonlocal i
  t=tokens[i];i+=1
  if t=='(':
   op=tokens[i];i+=1;args=[]
   while tokens[i]!=')':args.append(visit())
   i+=1;return(op,*args)
  if t=='[':
   xs=[]
   while tokens[i]!=']':
    xs.append(visit())
    if tokens[i]==';':i+=1
   i+=1;return xs
  return t
 v=visit();assert i==len(tokens),(i,len(tokens));return v


class Emitter:
 def __init__(self,ids):
  self.ids=ids
  self.counter=0

 def fresh(self,stem):
  self.counter+=1
  return stem+str(self.counter)

 def comp_list(self,xs,fuel,env):
  emit=self.emit;comp_list=self.comp_list;fresh=self.fresh
  if not xs:return 'Done []'
  a=emit(xs[0],fuel,env);b=comp_list(xs[1:],fuel,env);x=fresh('v');ys=fresh('vs');r=fresh('err')
  return f'(match {a}, {b} with |Done {x},Done {ys}=>Done({x}::{ys})|Missing {r},_=>Missing {r}|_,Missing {r}=>Missing {r}|_,_=>Stuck end)'

 def emit(self,e,fuel,env):
  emit=self.emit;comp_list=self.comp_list;fresh=self.fresh;ids=self.ids
  op,*a=e;k=fresh('k');r=fresh('err');x=fresh('x');y=fresh('y')
  def child(e):return emit(e,k,env)
  if op=='EVar':body=f'match lookup {a[0]} {env} with Some {x}=>Done {x}|None=>Missing "unbound variable" end'
  elif op=='ESymbol':body=f'Done(Symbol {a[0]})'
  elif op=='ENil':body=f'bind_computation {child(a[1])} (fun {x}=>match nilof {a[0]} (Some {x}) with Some {y}=>Done {y}|None=>Missing("nil "++{a[0]}) end)'
  elif op in ('EApply','EEq','EIsEq'):
   ok=f'Apply {x} {y}' if op=='EApply' else f'bool_term(term_eqb {x} {y})'
   stuck='Done(bool_term false)' if op=='EIsEq' else 'Stuck'
   body=f'match {child(a[0])},{child(a[1])} with |Done {x},Done {y}=>Done({ok})|Missing {r},_=>Missing {r}|_,Missing {r}=>Missing {r}|_,_=>{stuck} end'
  elif op=='EIsOk':body=f'match {child(a[0])} with |Done _=>Done(bool_term true)|Stuck=>Done(bool_term false)|Missing {r}=>Missing {r} end'
  elif op=='EIf':body=f'match {child(a[0])} with |Done(Symbol "true")=>{child(a[1])}|Done(Symbol "false")=>{child(a[2])}|Missing {r}=>Missing {r}|_=>Stuck end'
  elif op=='ERequires':body=f'match {child(a[0])},{child(a[1])} with |Done {x},Done {y}=>if term_eqb {x} {y} then {child(a[2])} else Stuck|Missing {r},_=>Missing {r}|_,Missing {r}=>Missing {r}|_,_=>Stuck end'
  elif op=='ETypeof':body=f'bind_computation {child(a[0])} (fun {x}=>match typeof {x} with Some {y}=>Done {y}|None=>Missing "eo::typeof" end)'
  elif op=='ELet':body=f'bind_computation {child(a[1])} (fun {x}=>{emit(a[2],k,f"(({a[0]},{x})::{env})")})'
  elif op=='ENative':body=f'native_result nilof typeof extra cpc_operators {a[0]} {comp_list(a[1],k,env)}'
  elif op=='ECall':
   name=a[0][1:-1].replace('""','"')
   if name not in ids:body=f'Missing("program "++{a[0]})'
   else:body=f'match {comp_list(a[1],k,env)} with |Done {x}=>{ids[name]} {k} {x}|Missing {r}=>Missing {r}|_=>Stuck end'
  else:raise ValueError(op)
  return f'(match {fuel} with |0=>Missing "fuel exhausted"|S {k}=>{body} end)'
