abstract sig Permissao {}

one sig Leitura, Escritaleitura, Dono extends Permissao {} 

abstract sig Objeto {
	todos: lone Permissao,
	externo: lone Permissao,
	local: lone Permissao -- Neste Computador
}

sig Arquivo extends Objeto {}

abstract sig Diretorio extends Objeto {
	conteudo: set Objeto
}

one sig Root extends Diretorio {}

sig Pasta extends Diretorio {
	pai: one Diretorio -- equivalente ao "/.." ?
}

fact{
	no p: Pasta | Root in p.conteudo -- nenhuma pasta contem Root
	all a: Arquivo | a in Diretorio.conteudo -- todo arquivo esta dentro de algum diretorio
}
---------------
pred test {
	some Objeto
}

run test for 5
