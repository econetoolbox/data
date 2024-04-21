library(igraph)
library(dplyr)
#load the food web data
foodwebs<-read.table("intertidal_rock_pools.txt",header=TRUE,sep="\t")


#create a list of all the food webs from the intertidal rocky pools
listweb<-unique(foodwebs$foodweb.name)
listweb

#Built food webs from the data
#example of code to select the first food web of the list, and
#get the food web as a igraph object or as a matrix format
web1<-subset(foodwebs,foodweb.name==listweb[1])
interweb1<-subset(web1,select=c("res.taxonomy","con.taxonomy"))
g<-graph_from_data_frame(interweb1,directed=TRUE)
matweb1<-as_adjacency_matrix(g,sparse=FALSE)

#Get species traits in the food webs
#example of code to get the species traits
#for the first food web of the list
web1<-subset(foodwebs,foodweb.name==listweb[1])
traitconso<-subset(web1,select=c("con.taxonomy","con.metabolic.type","con.movement.type","con.mass.mean.g."))
names(traitconso)<-c("taxonomy","metabolic.type","movement.type","mass.mean.g")
traitres<-subset(web1,select=c("res.taxonomy","res.metabolic.type","res.movement.type","res.mass.mean.g."))
names(traitres)<-c("taxonomy","metabolic.type","movement.type","mass.mean.g")
traitfinal<-rbind(traitconso,traitres)
traitfinal<-traitfinal %>% distinct() 
