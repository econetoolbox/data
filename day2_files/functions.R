library(bipartite)
library(igraph)
library(FWebs)
library(vegan)
library(cheddar)
library(matlib)
library(sbm)
library(alluvial)
library(econetwork)
library(poweRlaw)

### Simulating food webs

cascade_matrix<-function(cc,nspecies){ #from Cohen-Newman-Briand's papers
	upper.tri(matrix(1,nrow=nspecies,ncol=nspecies), diag = FALSE)*matrix(rbinom(nspecies*nspecies,1,cc/nspecies),nrow=nspecies)
}

niche_matrix<-function(connectance,nspecies){ #Williams-Martinez model
	n_i<-runif(nspecies)
	r_i<-rbeta(nspecies,1,(1/(2*connectance))-1)
	r_i<-r_i*n_i
	c_i<-sapply(1:nspecies,function(x) runif(1,min=r_i[x]/2,max=n_i[x]))
	pred_function<-function(z_1,z_2){
		if((n_i[z_1]<=c_i[z_2]+0.5*r_i[z_2])&(n_i[z_1]>=c_i[z_2]-0.5*r_i[z_2])) {
			1
		}
		else{
			0
		}
	}
	mat<-sapply(1:nspecies,function(x) sapply(1:nspecies,function(y) pred_function(y,x)))
	list("matrix"=mat,"n"=n_i,"r"=r_i,"c"=c_i)
}

generate_DM_model<-function(n,prop_basal,quant_fun="qpois", ...){#generating the Dubart-Massol food web model (Massol et al. 2017)
	basal<-round(n*prop_basal)
	degs<-generate_degseq_unipartite(n,quant_fun,...)
	undirected<-sample_degseq(degs, method = "vl")
	gvc<-greedy_vertex_coloring(undirected)
	majority_color<-which(gvc==which.max(table(gvc)))
	if(length(majority_color)<basal){
		print("not enough nodes in the largest color to make basal species, ")
		print("the number of basal species is set to")
		print(length(majority_color))
		basal<-length(majority_color)
	}
	basal_sp<-sample(majority_color,basal)
	tr_levels<-apply(distances(undirected,v=basal_sp),2,min_without_inf)
	chain_length<-max(tr_levels)
	directed<-as.directed(undirected)
	for(i in 1:chain_length){
		previous_set<-which(tr_levels==i-1)
		current_set<-which(tr_levels==i)
		directed<-delete_edges(directed,E(directed) [current_set %->% previous_set])
	}
	mut_edges<-which_mutual(directed)
	directed_intraguild<-as.directed(as.undirected(subgraph.edges(directed,E(directed)[mut_edges],delete.vertices = FALSE)),mode="random")
	directed<-delete_edges(directed,E(directed) [mut_edges])
	directed<-union(directed,directed_intraguild)
	return(directed)
}

make_food_web_from_undirected<-function(undirected,basal){
	gvc<-greedy_vertex_coloring(undirected)
	majority_color<-which(gvc==which.max(table(gvc)))
	if(length(majority_color)<basal){
		print("not enough nodes in the largest color to make basal species, ")
		print("the number of basal species is set to")
		print(length(majority_color))
		basal<-length(majority_color)
	}
	basal_sp<-sample(majority_color,basal)
	tr_levels<-apply(distances(undirected,v=basal_sp),2,min_without_inf)
	chain_length<-max(tr_levels)
	directed<-as.directed(undirected)
	for(i in 1:chain_length){
		previous_set<-which(tr_levels==i-1)
		current_set<-which(tr_levels==i)
		directed<-delete_edges(directed,E(directed) [current_set %->% previous_set])
	}
	mut_edges<-which_mutual(directed)
	directed_intraguild<-as.directed(as.undirected(subgraph.edges(directed,E(directed)[mut_edges],delete.vertices = FALSE)),mode="random")
	directed<-delete_edges(directed,E(directed) [mut_edges])
	directed<-union(directed,directed_intraguild)
	return(directed)
}


### Simulating a (B_)EDD network

leqone_mat<-function(x){# x is a matrix #function to generate a matrix of positive elements always less than 1
	d<-dim(x)
	matrix(sapply(x,function(u) ifelse(u>1,1,u)),nrow=d[1],ncol=d[2])
}

SimulB_EDD <- function(m, n, rho, lambda.g, lambda.h){#m is the number of row species, n the nb of column, rho the connectance, lambda.g the parameter for the rows, lambda.h for the columns, Ouadah-Latouche-Robin's algo
   # Simulation of B-EDD
   u <- runif(m); v <- runif(n)
   p <- rho * (lambda.g * u^(lambda.g-1)) %o% (lambda.h * v^(lambda.h-1))
   p<-leqone_mat(p)
   return(list(u=u, v=v, prob=p, net=matrix(rbinom(n*m, 1, p), m, n)))
}

Simul_EDD <- function(m, rho, lambda){#m is the number of  species, rho the connectance, lambda the parameter, Ouadah-Latouche-Robin's algo
   # same as above for EDD (unipartite graphs)
   u <- runif(m); 
   p <- rho * (lambda * u^(lambda-1)) %o% (lambda * u^(lambda-1))
   p<-leqone_mat(p)
   res<-matrix(rbinom(m*m, 1, p), m, m)
   res[lower.tri(res,diag=T)] <- 0
   res <- res + t(res)
   return(list(u=u, prob=p, net=res))
}

randomize.BChungLu<-function(bipmat){ #bipmat is an existing bipartite matrix, the function randomizes it with the aim of keeping the expected degrees
  s<-sum(bipmat)
  m1<-apply(bipmat,1,sum)
  m2<-apply(bipmat,2,sum)
  if(max(m1)*max(m2) > s) {
    print("Warning, some probabilities are higher than 1")
  }
  p<-leqone_mat(m1%o%m2/s)
  apply(p,c(1,2),function(x) rbinom(1,size = 1,prob = min(x,1)))
}

randomize.BEDD<-function(bipmat){ #same as Chung-Lu, but using distributions of degrees rather than actual degrees
	s<-sum(bipmat)
	m1<-apply(bipmat,1,sum)
	d1<-length(m1)
	m2<-apply(bipmat,2,sum)
	d2<-length(m2)
	rho<-s/(d1*d2)
	mset1<-ecdf(m1*d2/s)
	mset2<-ecdf(m2*d1/s)
	sample1<-quantile(mset1,probs=runif(d1))
	sample2<-quantile(mset2,probs=runif(d2))
	p <- rho * sample1 %o% sample2
	p<-leqone_mat(p)
	matrix(rbinom(d1*d2, 1, p), d1, d2)
}

randomize.EDD<-function(graph){ #same as above on undirected graphs
	if(is_directed(graph)){
		graph<-as.undirected(graph)
	}
	adjmat<-as_adj(graph,sparse=FALSE)
	s<-sum(adjmat)
	m<-apply(adjmat,1,sum)
	d<-dim(adjmat)[1]
	rho<-2*s/(d*(d-1))
	mset<-ecdf(m*d/s)
	sample_expdegs<-quantile(mset,probs=runif(d))
	p <- rho * sample_expdegs %o% sample_expdegs
	p<-leqone_mat(p)
	res<-matrix(rbinom(d*d, 1, p), d, d)
	res[lower.tri(res,diag=T)] <- 0
	res <- res + t(res)
	graph_from_adjacency_matrix(res)
}


generate.ChungLu<-function(ED1,ED2){ #ED1 and ED2 are the vectors of expected degrees
  s1<-sum(ED1)
  s2<-sum(ED2)
  if(s1 != s2) {
    print("Warning, the two sequences have different sums")
  }
  s<-max(s1,s2)
  if(max(ED1)*max(ED2) > s) {
    print("Warning, some probabilities are higher than 1")
  }
  p<-leqone_mat(ED1%o%ED2/s)
  apply(p,c(1,2),function(x) rbinom(1,size = 1,prob = min(x,1)))
}


### bipartite utilities

union_bipartite<-function(list_nets){
	x<-do.call(igraph::union, list_nets)
	l<-length(list_nets)
	type_vec<-sapply(1:l,function(y) paste0("type_",y))
	or_types<-apply(sapply(1:l, function(k) vertex_attr(x, type_vec[k])),1,any)
	V(x)$type<-!(is.na(or_types)|!(or_types))
	x
}

### food web utilities

# for classic trophic level computations, use the 'cheddar' package, for instance ShortestTrophicLevel

as_Community<-function(network,net_name="."){#takes a directed network (with species names) and make it a Community object for cheddar
	names_net<-V(network)$name
	nodes<-data.frame("node"=names_net,row.names= names_net)
	properties=list("title"=net_name)
	tlinks<-as_long_data_frame(network)
	trophic.links<-as.matrix(tlinks[,c("from_name","to_name")])
	colnames(trophic.links)<-c("resource", "consumer")
	Community(nodes, properties, trophic.links)
}
#example: ShortestTrophicLevel(as_Community(network,"WTF"))

trophic_levels<-function(network) { #based on MacKay et al. 2020
	lap<-corrected_laplacian(network)
	imbalance<-degree(network,mode="in")-degree(network,mode="out")
	inv(as.matrix(lap)) %*% imbalance
}

FW_interaction_from_predation<-function(mat,rho){
	n<-dim(mat)[1]
	fill<-rnorm_multi(n*(n-1)/2,2,r=rho)
	ut<-matrix(0,n,n)
	ut[lower.tri(ut,diag = FALSE)]<-fill[,1]
	ut<-mat*t(ut)
	lt<-matrix(0,n,n)
	lt[lower.tri(lt, diag = FALSE)]<-fill[,2]
	lt<-(t(mat))*lt
	ut+lt
}

layout_as_food_web<-function(network){#adapted from Jon Borelli's code https://assemblingnetwork.wordpress.com/2013/04/03/more-food-web-plotting-with-r/
	l<-length(V(network))
	lay<-matrix(nrow=l,ncol=2) 
	lay[,1]<-layout_with_graphopt(network)[,1]
	lay[,2]<-TrophicLevels(as_Community(network))[,5]-1
	lay
}

layout_as_food_web2<-function(network){#adapted from Jon Borelli's code https://assemblingnetwork.wordpress.com/2013/04/03/more-food-web-plotting-with-r/
	l<-length(V(network))
	lay<-matrix(nrow=l,ncol=2) 
	lay[,1]<-layout_with_graphopt(network)[,1]
	lay[,2]<-trophic_levels(network)
	lay
}

layout_as_food_web3<-function(network){#adapted from Jon Borelli's code https://assemblingnetwork.wordpress.com/2013/04/03/more-food-web-plotting-with-r/
	l<-length(V(network))
	lay<-matrix(nrow=l,ncol=2) 
	lay[,1]<-layout_with_graphopt(network)[,1]
	lay[,2]<-alt_TL(network)[,3]
	lay
}

alt_TL<-function(network){ #yet another implementation of trophic levels
	undir_net<-as.undirected(network)
	basals<-which(degree(network,mode="in")==0)
	dist_mat<-t(distances(network,v=which(degree(network,mode="in")==0),mode="out"))
	s<-dim(dist_mat)[1]
	shortest_chain<-sapply(1:s,function(x) min_without_inf(dist_mat[x,]))+1
	longest_chain<-sapply(1:s,function(x) max_without_inf(dist_mat[x,]))+1
	average_chain<-sapply(1:s,function(x) mean_without_inf(dist_mat[x,]))+1
	if(!is.null(V(network)$name)){
		res<-data.frame("species"=V(network)$name,"shortest"=shortest_chain,"longest"=longest_chain,"average" = average_chain)
	}
	else{
		res<-data.frame("shortest"=shortest_chain,"longest"=longest_chain,"average" = average_chain)
	}
	res
}


### other utilities
min_without_inf<-function(vec){
	min(vec[!is.infinite(vec)])
}

max_without_inf<-function(vec){
	max(vec[!is.infinite(vec)])
}

mean_without_inf<-function(vec){
	mean(vec[!is.infinite(vec)])
}

p.val<-function(test_val,test_collection,method="larger",label=""){#compute a p-value for a test based on a collection of values simulated using a null model
	test_collection<-c(test_collection,test_val)
	n<-length(test_collection)
	cumul<-ecdf(test_collection)
	mmin<-min(test_collection)
	mmax<-max(test_collection)
	plot(density(test_collection),xlim=c(mmin,mmax),main=label,xlab="")
	abline(v=test_val,col="red")
	if(method=="lower"){
		max(cumul(test_val),1/n)
	}
	else if(method=="two-sided"){
		max(2*min(cumul(test_val),1-cumul(test_val)),1/n)
	}
	else{
		max(1-cumul(test_val),1/n)
	}
	
}

corrected_laplacian<-function(network){
	lap<-laplacian_matrix(network)
	lap+diag(degree(network,mode="in"))
}

to_upper_triangular<-function(mat){
	upper.tri(mat, diag = FALSE)*mat
}

make_alluvial_2<-function(classif1,classif2,name1,name2){
	A <- as.data.frame(table(classif1,classif2))
	colnames(A) = c(name1,name2,"Freq")
	w   <- which(A$Freq != 0)
	A <- A[w,]
	alluvial(A[,c(1,2)],freq = A$Freq)
}

qtrunc <- function(p, spec, a = -Inf, b = Inf, ...){#copied from Nadarajah & Kotz 2006
	tt <- p
	G <- get(paste("p", spec, sep = ""), mode = "function")
	Gin <- get(paste("q", spec, sep = ""), mode = "function")
	tt <- Gin(G(a, ...) + p*(G(b, ...) - G(a, ...)), ...)
	return(tt)
}

spectral_clustering <- function(graph, nb_cluster, normalized = TRUE) {#from J. Chiquet's git page https://jchiquet.github.io/MAP566/docs/mixture-models/map566-lecture-graph-clustering-part1.html
  
  ## Compute Laplcian matrix
  L <- laplacian_matrix(graph, normalized = normalized) 
  ## Generates indices of last (smallest) K vectors
  selected <- rev(1:ncol(L))[1:nb_cluster] 
  ## Extract an normalized eigen-vectors
  U <- eigen(L)$vectors[, selected, drop = FALSE]  # spectral decomposition
  U <- sweep(U, 1, sqrt(rowSums(U^2)), '/')    
  ## Perform k-means
  res <- kmeans(U, nb_cluster, nstart = 40)$cl
  
  res
}

laplacian_spectral_gap<- function(graph){
	L <- laplacian_matrix(graph, normalized = TRUE)
	comps<-count_components(graph)
	lambdas <- sort(eigen(L)$values)
	l<-length(lambdas)
	s_gaps<-lambdas[-1]-lambdas[-l]
	s_util<-s_gaps[-(1:comps)]
	s_util<-s_util[1:round(l/2)]
	opt_n<-which.max(s_util)+comps
	
	par(mfrow=c(2,1))
	plot(lambdas,xlab="",ylab="lambda",type="l")
	plot(s_gaps,xlab="",ylab="spectral gap",type="l")
	
	list("spectral_gaps"=s_gaps,"optim_n"=opt_n)
}

### degree sequence utilities
generate_degseq_unipartite<-function(n,quant_fun="qpois", ...){
	p_s<-(1:n-0.5)/n
	d_s<-get(quant_fun)(p=p_s,...)
	#print(d_s)
	if(!is_graphical(d_s)){
		sp<-substring(quant_fun,first=2)
		trun<-1
		while(!is_graphical(d_s)){
			trun<-trun+1
			d_s<-qtrunc(p=p_s,spec = sp, a=trun, ...)
		}
		d_s
	}
	else{
		d_s
	}
}

### configuration model

config_VL<-function(graph,nsim = 100){#configuration model for binary networks; built upon vegan and igraph
	if(is_igraph(graph)){
		if((is_weighted(graph))||(!is_simple(graph))){
			print("graph is not simple, can't do")
		}
		else if(is_bipartite(graph)){
			print("bipartite graph detected")
			incidence<-as.matrix(as_biadjacency_matrix(graph))
			configs<-simulate(vegan::nullmodel(incidence,"curveball"),nsim=nsim) 
			lapply(1:nsim,function(x) graph_from_biadjacency_matrix(configs[,,x]))
		}
		else{
			print("unipartite graph detected")
			lapply(1:nsim, function(x) sample_degseq(degree(graph), method = "vl"))
		}
	}
	else if(is.matrix(graph)){
		d<-dim(graph)
		if(max(graph)>1){
			print("graph is not simple, can't do")
		}
		else if(d[1]==d[2]){
			print("unipartite graph detected")
			config_VL(graph_from_adjacency_matrix(graph),nsim)
		}
		else{
			print("bipartite graph detected")
			configs<-simulate(vegan::nullmodel(graph,"curveball"),nsim=nsim) 
			lapply(1:nsim,function(x) graph_from_biadjacency_matrix(configs[,,x]))
		}
	}
	else{
		config_VL(as.matrix(graph),nsim)
	}
}
