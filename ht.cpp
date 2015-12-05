#include <iostream>
using namespace std;

class Node{
  pair<string,string> keyNvalue;
  Node* next = NULL;

  public:
    Node(){}
    Node(pair<string,string> d){
      keyNvalue = d;
    }
    void appendToTail(pair<string,string> d){
      Node* end = new Node(d);
      Node* n = this;
      while(n->next != NULL){
        n = n->next;
      }
      n->next = end;
    }
    string getVal(string key){
      Node* n = this;
      while(n != NULL){
        pair<string,string> p = n->keyNvalue;
        string k1 = get<0>(p);
        if(key==k1)
          return get<1>(p);
        if(n->next != NULL)
          n = n->next;
        else break;
      }
      return "";
    }
};

class hashtable{
  Node array[100];
  private:
    int hash(string key){
      int ind = 13;
      for(int i=0;i<key.length();i++){
        ind+=(key[i])%13;
      }
      return ind;
    }
    void insertInHash(int ind, pair<string,string> p){
      array[ind].appendToTail(p);
    }
  public:
    hashtable(){

    }
  void insert(string key, string value){
    insertInHash(hash(key), make_pair(key,value));
  }
  string find(string key){
    return array[hash(key)].getVal(key);
  }
};

int main(){
  hashtable ht;
  ht.insert("Maksim", "Celine");
  ht.insert("Janet", "Angel");
  ht.insert("Eva", "Sister");
  cout<<ht.find("Eva")<<endl;
  return 0;
}
