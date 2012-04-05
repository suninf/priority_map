/*
author: zhenshan
description: 
	* combine map with priority_queue, make it easy to modify the priority of the key in real-time way
	* especially useful in the situation of dynamic priority with keys
*/
#ifndef PRIORITY_MAP
#define PRIORITY_MAP

#include <functional>
#include <utility>
#include <vector>
#include <boost/shared_ptr.hpp>
#include <boost/unordered_map.hpp>
#include <boost/utility.hpp>

namespace priority_map_detail
{
	// array node
	template<typename KeyType, typename ValType, bool UseRef>
	struct queue_node 
	{
		KeyType const&  first;		// use the key of hash_map
		ValType			second;		// value

		queue_node( KeyType const& key, ValType const& val = ValType() )
			: first( key ), second( val )
		{}
	};

	template<typename KeyType, typename ValType>
	struct queue_node< KeyType, ValType, false >
	{
		KeyType  first;		// copy the key of hash_map
		ValType	second;		// value

		queue_node( KeyType const& key, ValType const& val = ValType() )
			: first( key ), second( val )
		{}
	};

	// ref pair
	template<typename T, typename U>
	struct RefPair 
	{
		T const& first;
		U const& second;

		RefPair( T const& key, U const& val ) :
		first(key), second(val)
		{}
	};

	// bool to type
	template<bool>
	struct bool2type {};

}// priority_map_detail

// forward declaration
template
<
	typename KeyType,	// key
	typename ValType,	// value
	typename ValComp = std::less< ValType >,		// for priority_queue
	bool	 UseRef  = true,						// use ref of key of hash_map or not
	typename KeyHash = boost::hash<KeyType>,		// for hash_map map key to index
	typename KeyComp = std::equal_to<KeyType>		// for hash_map compare key
>
class priority_map;

// implement
template
<
	typename KeyType,
	typename ValType,
	typename ValComp,
	bool	 UseRef,
	typename KeyHash,
	typename KeyComp
>
class priority_map
{
	typedef boost::unordered_map< KeyType, int, KeyHash, KeyComp > HashMapType;
public:
	// typedefs
	typedef priority_map_detail::queue_node<KeyType,ValType,UseRef> value_type;
	typedef value_type*			pointer;
	typedef const value_type*	const_pointer;
	typedef value_type&			reference;
	typedef value_type const&	const_reference;

	template<typename Iter>
	struct iterator_impl
	{
		iterator_impl( Iter const& it ) :
			iter_( it )
		{}

		const_pointer operator->() const
		{
			return (*iter_).get();
		}

		const_reference operator * () const
		{
			return *(*iter_).get();
		}

		iterator_impl& operator++()
		{
			++iter_;
			return *this;
		}

		iterator_impl operator++(int) const
		{
			iterator_impl tmp(*this);
			++iter_;
			return tmp;
		}

		iterator_impl& operator += ( int n )
		{
			iter_ += n;
			return *this;
		}

		iterator_impl operator + ( int n ) const
		{
			iterator_impl tmp(*this);
			tmp += n;
			return tmp;
		}

		iterator_impl& operator--()
		{
			--iter_;
			return *this;
		}

		iterator_impl operator--(int) const
		{
			iterator_impl tmp(*this);
			--iter_;
			return tmp;
		}

		iterator_impl& operator -= ( int n )
		{
			iter_ -= n;
			return *this;
		}

		iterator_impl operator - ( int n ) const
		{
			iterator_impl tmp(*this);
			tmp -= n;
			return tmp;
		}

		// compare
		bool operator == ( iterator_impl const& rhs ) const
		{
			return iter_ == rhs.iter_;
		}

		bool operator != ( iterator_impl const& rhs ) const
		{
			return iter_ != rhs.iter_;
		}

	private:
		Iter iter_;
	};

	// iterator could not modify the value
	typedef iterator_impl< typename std::vector< boost::shared_ptr<value_type> >::const_iterator > 
						iterator;
	typedef iterator	const_iterator;

	struct SPValComp 
	{
		bool operator()( boost::shared_ptr<value_type> const& lhs, 
			boost::shared_ptr<value_type> const& rhs ) const
		{
			return comp_( lhs->second, rhs->second );
		}

		bool operator()( value_type const& lhs, value_type const& rhs ) const
		{
			return comp_( lhs.second, rhs.second );
		}

		bool operator()( ValType const& lhs, ValType const& rhs ) const
		{
			return comp_( lhs, rhs );
		}

		ValComp comp_;
	};

public:
	// constructor and assign etc.
	priority_map()
	{}

	// because of queue_node, we define Key const&, 
	// default behavior of copy constructor should change
	priority_map( priority_map const& rhs )
	{
		_Copy( rhs, priority_map_detail::bool2type<UseRef>() );
	}

	template<typename Container>
	explicit priority_map( Container const& cont )
	{
		typedef typename Container::const_iterator Iter;

		int index = 0;
		for ( Iter it = cont.begin(); it != cont.end(); ++it, ++index )
		{
			std::pair<HashMapType::iterator, bool>
				pr = m_hashMap.insert( HashMapType::value_type( it->first, index ) );
			if ( pr.second )
			{
				m_priQueue.push_back( boost::shared_ptr<value_type>( new value_type( pr.first->first, it->second ) ) );
			}
		}
		_BuildHeap();
	}

	template<typename Iter>
	priority_map( Iter beg, Iter end )
	{		
		int index = 0;
		for ( Iter it = beg; it != end; ++it, ++index )
		{
			std::pair<HashMapType::iterator, bool>
				pr = m_hashMap.insert( HashMapType::value_type( it->first, index ) );
			if ( pr.second )
			{
				m_priQueue.push_back( boost::shared_ptr<value_type>( new value_type( pr.first->first, it->second ) ) );
			}
		}
		_BuildHeap();
	}

	priority_map& operator = ( priority_map const& rhs )
	{
		if ( this != &rhs )
		{
			clear();
			_Copy( rhs, priority_map_detail::bool2type<UseRef>() );
		}
		return *this;
	}

public:
	// operations for priority queue

	// push: equal to update
	template<typename Pair>
	void push( Pair const& val )
	{
		return update<Pair>( val );
	}

	void push( KeyType const& key, ValType const& val )
	{
		return update( key, val );
	}
	
	/*@ top 
	* return the reference of <Key,Value> of the largest priority 
	* the conttent should not be empty
	*/
	const_reference top() const
	{
		return *(m_priQueue[0].get());
	}

	/*@ pop
	* remove the top member
	*/
	void pop()
	{
		if ( m_priQueue.empty() )
			return;

		if ( m_priQueue.size() == 1 )
		{
			clear();
			return;
		}

		erase( m_priQueue[0]->first );
	}

public:
	// operations for iterator
	iterator begin() const
	{
		return iterator( m_priQueue.begin() );
	}

	iterator end() const
	{
		return iterator( m_priQueue.end() );
	}

public:
	// operations for map
	size_t size() const { return m_hashMap.size(); }
	bool empty() const { return m_hashMap.empty(); }

	/*@ insert
	* return true if insert success, or else false if already exist
	*/
	template<typename Pair>
	bool insert( Pair const& val )
	{
		std::pair<HashMapType::iterator, bool>
			pr = m_hashMap.insert( HashMapType::value_type( val.first, m_priQueue.size() ) );
		if ( pr.second )
		{
			m_priQueue.push_back( boost::shared_ptr<value_type>( new value_type( pr.first->first, val.second ) ) );
		}
		else
			return false;
		
		// insert and percolate up
		_PercUp( m_priQueue.size()-1 );
		return true;
	}

	bool insert( KeyType const& key, ValType const& val )
	{
		return insert( priority_map_detail::RefPair<KeyType,ValType>( key, val ) );
	}

	template<typename Iter>
	void insert( Iter beg, Iter end )
	{
		for ( Iter it = beg; it != end; ++it )
		{
			insert( *it );
		}
	}

	/*@ replace
	* return true if replace success, or else false if not exist
	*/
	template<typename Pair>
	bool replace( Pair const& val )
	{
		HashMapType::iterator it = m_hashMap.find( val.first );
		if ( it == m_hashMap.end() )
			return false;

		if ( m_ValComp( val.second, m_priQueue[it->second]->second ) )
		{
			// percolate down
			m_priQueue[it->second]->second = val.second;
			_PercDown( it->second );
		}
		else
		{
			m_priQueue[it->second]->second = val.second;
			_PercUp( it->second );
		}
		return true;
	}

	bool replace( KeyType const& key, ValType const& val )
	{
		return replace( priority_map_detail::RefPair<KeyType,ValType>( key, val ) );
	}

	template<typename Iter>
	void replace( Iter beg, Iter end )
	{
		for ( Iter it = beg; it != end; ++it )
		{
			replace( *it );
		}
	}

	/*@ update
	* replace if exist, or else insert
	*/
	template<typename Pair>
	void update( Pair const& val )
	{
		HashMapType::iterator it = m_hashMap.find( val.first );
		if ( it != m_hashMap.end() )
		{
			// exist replace
			if ( m_ValComp( val.second, m_priQueue[it->second]->second ) )
			{
				m_priQueue[it->second]->second = val.second;
				_PercDown( it->second );
			}
			else
			{
				m_priQueue[it->second]->second = val.second;
				_PercUp( it->second );
			}
		}
		else
		{
			// insert
			std::pair<HashMapType::iterator, bool>
				pr = m_hashMap.insert( HashMapType::value_type( val.first, m_priQueue.size() ) );
			if ( pr.second )
			{
				m_priQueue.push_back( boost::shared_ptr<value_type>( new value_type( pr.first->first, val.second ) ) );
				_PercUp( m_priQueue.size()-1 );
			}
		}
	}

	void update( KeyType const& key, ValType const& val )
	{
		update( priority_map_detail::RefPair<KeyType,ValType>( key, val ) );
	}

	template<typename Iter>
	void update( Iter beg, Iter end )
	{
		for ( Iter it = beg; it != end; ++it )
		{
			update( *it );
		}
	}

	// find
	iterator find( KeyType const& key ) const
	{
		HashMapType::const_iterator cit = m_hashMap.find(key);
		if ( cit != m_hashMap.end() )
		{
			return iterator(m_priQueue.begin() + cit->second);
		}

		return end();
	}

	// erase
	void erase( KeyType const& key )
	{
		HashMapType::iterator it = m_hashMap.find( key );
		if ( it != m_hashMap.end() )
		{
			int idx = it->second;
			if ( idx == m_priQueue.size()-1 ) // the last one
			{
				m_hashMap.erase( it );
				m_priQueue.pop_back();
			}
			else
			{
				m_hashMap.erase( it );
				ValType val = m_priQueue[idx]->second;

				// move the last leaf to replace
				boost::shared_ptr<value_type> last_node = m_priQueue[ m_priQueue.size()-1 ];
				m_hashMap[ last_node->first ] = idx;
				m_priQueue[idx] = last_node; // previous shared_ptr destroy
				m_priQueue.pop_back();

				// and then percolate down/up
				if ( m_ValComp( val, last_node->second ) )
				{
					_PercUp( idx );
				}
				else
				{
					_PercDown( idx );
				}
			}
		}
	}

	void clear()
	{
		m_hashMap.clear();
		m_priQueue.clear();
	}

	/*@ swap
	* could not use std::swap(member, rhs.member), 
	* also because of queue_node, we define Key const&, 
	* swap is not so fast
	*/
	void swap( priority_map& rhs )
	{
		_Swap( rhs, priority_map_detail::bool2type<UseRef>() );
	}

private:
	// inner functions
	static int _LeftChild(int n)
	{
		return 2*n + 1;
	}

	static int _Father(int n)
	{
		if ( n == 0 )
			return -1;

		return (n%2==0 ? n/2 : (n+1)/2) - 1;
	}

	void _BuildHeap()
	{
		for ( int i = _Father( (int)m_priQueue.size()-1 ); i>=0; --i )
		{
			_PercDown( i );
		}
	}

	void _PercDown( int i ) // percolate down the n-th element
	{
		int child = 0;
		boost::shared_ptr<value_type> tmp = m_priQueue[i];
		for ( ; _LeftChild(i) < (int)m_priQueue.size(); i = child )
		{
			child = _LeftChild(i);
			if ( child != m_priQueue.size()-1 && m_ValComp( m_priQueue[child], m_priQueue[child+1] ) )
			{
				++child;
			}
			if ( m_ValComp( tmp, m_priQueue[child] ) )
			{
				m_priQueue[i] = m_priQueue[child];
				m_hashMap[ m_priQueue[i]->first ] = i;	//update index 
			}
			else
				break;
		}
		m_priQueue[i] = tmp;
		m_hashMap[ m_priQueue[i]->first ] = i;
	}

	void _PercUp( int i )
	{
		boost::shared_ptr<value_type> tmp = m_priQueue[i];
		for ( ; _Father(i) >= 0 && m_ValComp( m_priQueue[_Father(i)], tmp ); i = _Father(i) )
		{
			m_priQueue[i] = m_priQueue[ _Father(i) ];
			m_hashMap[ m_priQueue[i]->first ] = i;
		}
		m_priQueue[i] = tmp;
		m_hashMap[ m_priQueue[i]->first ] = i;
	}

	// copy detail
	void _Copy( priority_map const& rhs, priority_map_detail::bool2type<true> )
	{
		int index = 0;
		for ( iterator it = rhs.begin(); it != rhs.end(); ++it, ++index )
		{
			std::pair<HashMapType::iterator, bool>
				pr = m_hashMap.insert( HashMapType::value_type( it->first, index ) );
			if ( pr.second )
			{
				m_priQueue.push_back( boost::shared_ptr<value_type>( new value_type( pr.first->first, it->second ) ) );
			}
		}
		_BuildHeap();
	}

	void _Copy( priority_map const& rhs, priority_map_detail::bool2type<false> )
	{
		m_hashMap = rhs.m_hashMap;
		m_priQueue = rhs.m_priQueue;
	}

	// swap detail
	void _Swap( priority_map & rhs, priority_map_detail::bool2type<true> )
	{
		priority_map tmp( *this );
		*this = rhs;
		rhs = tmp;
	}

	void _Swap( priority_map & rhs, priority_map_detail::bool2type<false> )
	{
		std::swap( m_hashMap, rhs.m_hashMap );
		std::swap( m_priQueue, rhs.m_priQueue );
	}

private:
	// value compare
	SPValComp m_ValComp;

	// priority queue
	std::vector< boost::shared_ptr<value_type> >		 m_priQueue;

	// hash_map: map key to index of queue
	HashMapType	 m_hashMap;
};


namespace std
{
	template
	<
		typename KeyType,
		typename ValType,
		typename ValComp,
		bool     UseRef,
		typename KeyHash,
		typename KeyComp
	>
	void swap( priority_map<KeyType,ValType, ValComp, UseRef, KeyHash, KeyComp>& lhs,
				priority_map<KeyType,ValType, ValComp, UseRef, KeyHash, KeyComp>& rhs ) 
	{
		lhs.swap( rhs );
	}

}// std



#endif//PRIORITY_MAP
