typedef int index_t;
typedef char value_t;

#define MAX_ITEMS ((sizeof(index_t)*8)+1)

index_t nondet_index();
value_t nondet_value();

value_t a(index_t n);
