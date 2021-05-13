abstract sig Permissao {}

one sig Leitura, EscritaLeitura, Dono extends Permissao {} 

-- Todo objeto (arquivo ou diretorio) define um unico tipo de permissao para todos os usuarios, um unico tipo de permissao para usuarios externos e um unico tipo de permissao para usuarios locais
abstract sig Objeto {
	todos: one Permissao,
	externo: one Permissao,
	local: one Permissao -- Neste Computador
}

sig Arquivo extends Objeto {}

abstract sig Diretorio extends Objeto {
	conteudo: set Objeto -- Todo diretorio tem um conjunto de objetos, o que significa que todo diretorio pode ter arquivos e diretorios dentro dele
}

one sig Root extends Diretorio {}

sig Pasta extends Diretorio {
	pai: one Diretorio -- equivalente ao "/.." do linux
}

abstract sig TipoDoUsuario {}

one sig Local, Externo extends TipoDoUsuario {} 

sig Usuario {
	permissoes: set (Objeto -> one Permissao),
	tipo: one TipoDoUsuario
}

fact pastas {
	no pasta: Pasta | Root in pasta.conteudo -- nenhuma pasta contem Root
	all arquivo: Arquivo | arquivo in Diretorio.conteudo -- todo arquivo esta dentro de algum diretorio
	all pasta: Pasta | Root in pasta.^pai -- Todas as pastas estao no nivel inferior a Root
	no diretorio: Diretorio | diretorio in diretorio.^conteudo or diretorio in diretorio.^pai -- O conteudo de um diretorio nunca pode apontar para ele mesmo ate o ultimo conteudo. Do mesmo modo, o pai de uma pasta nunca pode apontar para ela mesma ate o ultimo diretorio pai
	all diretorio: Diretorio | diretorio.^conteudo != diretorio.^pai -- O conteudo de uma pasta nunca pode apontar para o seu diretorio pai
	all pasta: Pasta | pasta in (pasta.pai).conteudo -- toda pasta tem que esta no conteudo do seu diretorio pai
	all pasta: Pasta | one pasta.~conteudo --toda pasta so pode esta em um diretorio	
	all arquivo: Arquivo | one arquivo.~conteudo -- todo arquivo so pode esta em um diretorio
}

fact permissoesUsuarios {	
	hierarquiaPermissao --hierarquia das permissoes
	
	all permissao: Permissao | permissaoRelacionadaObjeto[permissao] -- Toda permissao criada no modelo precisa estar relacionada a um objeto
	all usuario: Usuario | some usuario.permissoes -- Todo usuario criado no modelo precisa ter alguma permissao para alguma pasta, arquivo ou diretorio
	all tipoDoUsuario: TipoDoUsuario | tipoDoUsuario in Usuario.tipo -- Todo tipoDoUsuario criado no modelo precisa estar relacionado a um Usuario
	all objeto: Objeto, permissao: Permissao | apenasDonosAlteramPermissao[objeto, permissao]
}

fact objetos {
	all objeto: Objeto | garantirHierarquiaDePermissoes[objeto]
}

pred permissaoRelacionadaObjeto(permissao: Permissao) {
	permissao in Objeto.todos or permissao in Objeto.externo or permissao in Objeto.local
}

pred apenasDonosAlteramPermissao(objeto: Objeto, permissao: Permissao) {
	no usuario: Usuario | buscarPermissaoNoObjeto[objeto, usuario] != Dono and (alterarPermissaoTodos[objeto, permissao] or alterarPermissaoLocal[objeto, permissao] or alterarPermissaoExterno[objeto, permissao])
}

pred alterarPermissaoTodos(objeto: Objeto, permissao: Permissao) {
	objeto.todos = permissao
}

pred alterarPermissaoLocal(objeto: Objeto, permissao: Permissao) {
	objeto.local = permissao
}

pred alterarPermissaoExterno(objeto: Objeto, permissao: Permissao) {
	objeto.externo = permissao
}

fun buscarPermissaoNoObjeto(objeto: Objeto, usuario: Usuario): lone Permissao {
	objeto.(usuario.permissoes)
}

-- Um arquivo nunca pode ter, para uma determinada categoria de usuarios, uma permissao menos restrita do que um diretorio ancestral dele.
pred garantirHierarquiaDePermissoes(objeto: Objeto) {
	no objeto: Objeto | 
	(objeto.~conteudo.todos = Leitura and (objeto.todos = EscritaLeitura or objeto.todos = Dono))
	or
	(objeto.~conteudo.todos = EscritaLeitura and (objeto.todos = Dono))
	or
	(objeto.~conteudo.externo = Leitura and (objeto.externo = EscritaLeitura or objeto.externo = Dono))
	or
	(objeto.~conteudo.externo = EscritaLeitura and (objeto.externo = Dono))
	or
	(objeto.~conteudo.local = Leitura and (objeto.local = EscritaLeitura or objeto.local = Dono))
	or
	(objeto.~conteudo.local = EscritaLeitura and (objeto.local = Dono))
}

-- Um arquivo nunca pode ter, para uma determinada categoria de usuarios, uma permissao menos restrita do que um diretorio ancestral dele.
pred hierarquiaPermissao {
	-- permissao pastas dono
	no pasta: Pasta | pasta.todos = Dono and ((pasta.pai).todos = Leitura or (pasta.pai).todos = EscritaLeitura)
	no pasta: Pasta | pasta.local = Dono and ((pasta.pai).local = Leitura or (pasta.pai).local = EscritaLeitura)
	no pasta: Pasta | pasta.externo = Dono and ((pasta.pai).externo = Leitura or (pasta.pai).externo = EscritaLeitura)

	-- permissao pasta EscritaLeitura
	no pasta: Pasta | pasta.todos = EscritaLeitura and (pasta.pai).todos = Leitura
	no pasta: Pasta | pasta.local = EscritaLeitura and (pasta.pai).local = Leitura
	no pasta: Pasta | pasta.externo = EscritaLeitura and (pasta.pai).externo = Leitura

	--permissao arquivo todos
	all arquivo: Arquivo | ( 
		(arquivo.todos = Dono and (arquivo.~conteudo).todos = Dono) or 
		(arquivo.todos = EscritaLeitura and ( ((arquivo.~conteudo).todos = Dono) or ((arquivo.~conteudo).todos = EscritaLeitura)) ) or
		(arquivo.todos = Leitura)
	)
	
	--permissao arquivo externo
	all arquivo: Arquivo | ( 
		(arquivo.externo = Dono and (arquivo.~conteudo).externo = Dono) or 
		(arquivo.externo = EscritaLeitura and ( ((arquivo.~conteudo).externo = Dono) or ((arquivo.~conteudo).externo = EscritaLeitura)) ) or
		(arquivo.externo = Leitura)
	)

	--permissao arquivo local
	all arquivo: Arquivo | ( 
		(arquivo.local = Dono and (arquivo.~conteudo).local = Dono) or 
		(arquivo.local = EscritaLeitura and ( ((arquivo.~conteudo).local = Dono) or ((arquivo.~conteudo).local = EscritaLeitura)) ) or
		(arquivo.local = Leitura)
	)
}

fun quantidadeItensNaPasta(local: Diretorio): Int {
	#local.conteudo
}

fun caminhoDoObjeto(objeto: Objeto): set Diretorio {
	objeto.^(~conteudo)
}

--verifica se todo objeto tem Root como diretorio superior
assert herdaDeRoot {
	all objetoRoot: Objeto-Root | Root in caminhoDoObjeto[objetoRoot] --Root esta no caminho de todo os objetos, exceto o dele mesmo (Root não tem caminho)
}

--Verifica se um objeto pode esta em mais de 1 diretorio ao mesmo tempo
assert localDuplicado {
	no objeto: Objeto, diretorio1, diretorio2: Diretorio | diretorio1 != diretorio2 and objeto in diretorio1.conteudo and objeto in diretorio2.conteudo
}

--Verifica algumas opções de herança na permissao são respeitadas
assert herancaPermissao1 {
	no objeto: Objeto | objeto.local = EscritaLeitura and (objeto.~conteudo).local = Leitura
}

assert herancaPermissao2 {
	all arquivo: Arquivo | arquivo.todos = Dono implies caminhoDoObjeto[arquivo].todos = Dono
}

assert herancaPermissao3 {
	all pasta: Pasta | pasta.externo = Dono implies (pasta.^pai).externo = Dono
}

---------------


pred test {
	#Arquivo > 2
	#Pasta > 1
}

run test for 8

// check herancaPermissao for 8
