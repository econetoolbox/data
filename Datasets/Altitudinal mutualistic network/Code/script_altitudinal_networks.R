library(igraph)

#load the data: example for bird-fruit networks
webs<-read.csv("01BirdFruitInteractions.csv")


#create a list of all the study sites sampled
listweb<-unique(webs$plot)
listweb


#Built networks from the data
###function to create an incidence matrix -> apply to (.txt)
my.incidence<-function(gr){
  adj<-as.data.frame(as.matrix(as_adjacency_matrix(gr,attr="weight")))
  adj<-adj[order(names(adj)),order(names(adj))]
  I.index<-max(grep("A_",names(adj)))
  adj[1:I.index,(I.index+1):length(names(adj))]
}

#example of code to select the first network of the list, and
#get the network as a igraph object or as a matrix format
web1<-subset(webs,plot==listweb[1])
interweb1<-subset(web1,select=c("plant_species","animal_species","frequency"))
names(interweb1)[3]<-"weight"
interweb1$plant_species<-paste0("P_",interweb1$plant_species)
interweb1$animal_species<-paste0("A_",interweb1$animal_species)
g<-graph_from_data_frame(interweb1,directed=FALSE)
#create incidence matrix
my.incidence(g)
